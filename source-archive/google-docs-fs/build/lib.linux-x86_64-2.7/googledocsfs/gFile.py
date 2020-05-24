#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
#   gFile.py
#
#   Copyright 2008-2009 Scott C. Walton <d38dm8nw81k1ng@gmail.com>
#   truncate() function written by miGlanz@gmail.com
#
#   This program is free software; you can redistribute it and/or modify
#   it under the terms of the GNU General Public License (version 2), as
#   published by the Free Software Foundation
#
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program; if not, write to the Free Software
#   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
#   MA 02110-1301, USA.

import stat
import os
import sys
import threading
import platform
import errno
import time
import fuse
import gNet
import getpass

from subprocess import *

fuse.fuse_python_api = (0,2)

class GStat(fuse.Stat):
    """
    The stat class to use for getattr
    """
    def __init__(self):
        """
        Purpose: Sets the attributes to folder attributes
        Returns: Nothing
        """
        self.st_mode = stat.S_IFDIR | 0744
        self.st_ino = 0
        self.st_dev = 0
        self.st_nlink = 2
        self.st_uid = os.getuid()
        self.st_gid = os.getgid()
        self.st_size = 4096
        self.st_atime = time.time()
        self.st_mtime = self.st_atime
        self.st_ctime = self.st_atime

    def set_file_attr(self, size):
        """
        Purpose: Set attributes of a file
        size: int the file's size in bytes


        """
        self.st_mode = stat.S_IFREG | 0744
        self.st_nlink = 1
        self.st_size = size

    def set_access_times(self, mtime, ctime, atime = None):
        """
        Purpose: Set the access times of a file
        mtime: int modified time
        ctime: int creation time
        atime: int access time
        """
        self.st_mtime = mtime
        self.st_atime = ctime
        if atime is not None and atime > 0:
            self.st_atime = atime

class GFile(fuse.Fuse):
    """
    The main Google Docs filesystem class. Most work will be done
    in here.
    """

    def __init__(self, em, pw, *args, **kw):
        """
        Purpose: Connect to the Google Docs Server and verify credentials
        em: User's email address
        pw: User's password
        *args: Args to pass to Fuse
        **kw: Keywords to pass to Fuse
        Returns: Nothing
        """

        super(GFile, self).__init__(*args, **kw)
        self.gn = gNet.GNet(em, pw)
        self.directories = {}
        self.files = {}
        self.written = {}
        self.time_accessed = {}
        self.release_lock = threading.RLock()
        self.to_upload = {}
        self.codec = 'utf-8'
        self.home = unicode('%s/.google-docs-fs' % (os.path.expanduser('~'),), self.codec)
        if os.uname()[0] == 'Darwin':
            self.READ = 0
            self.WRITE = 1
            self.READWRITE = 2
        else:
            self.READ = 32768
            self.WRITE = 32769
            self.READWRITE = 32770

        self.APPEND = 337932
        self.APPENDRW = 33794

    def getattr(self, path):
        """
        Purpose: Get information about a file
        path: String containing relative path to file using mountpoint as /
        Returns: a GStat object with some updated values
        """

        path = unicode(path, self.codec)
        filename = os.path.basename(path)
                
        if '/' not in self.files:
            self.files['/'] = GStat()
            
        if path in self.files:
            st = self.files[path]
        elif filename[0] == '.':
            st = os.stat(('%s%s' % (self.home, path)).encode(self.codec))
        else:
            f = self.gn.get_filename(path, 'true')
            if f is None:
                return -errno.ENOENT
            self._setattr(path = path, entry = f)
            st = self.files[path]
        
        return st

    def readdir(self, path, offset):
        """
        Purpose: Give a listing for ls
        path: String containing relative path to file using mountpoint as /
        offset: Included for compatibility. Does nothing
        Returns: Directory listing for ls
        """
        dirents = ['.', '..']
        path = unicode(path, self.codec)
        filename = os.path.basename(path)

        if path == '/': # Root
            excludes = []
            self.directories['/'] = []
            feed = self.gn.get_docs(filetypes = ['folder'])
            for dir in feed.entry:
                excludes.append('-' + dir.title.text.decode(self.codec))
                self.directories['%s%s' % (path, dir.title.text.decode(self.codec))] = []
            if len(excludes) > 0:
                i = 0
                while i < len(excludes):
                    excludes[i] = excludes[i].encode(self.codec)
                    i += 1
                feed = self.gn.get_docs(filetypes = excludes)
            else:
                feed = self.gn.get_docs() # All must be in root folder
                
            for file in feed.entry:
                if file.GetDocumentType() == 'folder':
                    self.directories['/'].append('%s' % (file.title.text.decode(self.codec), ))
                else:
                    self.directories['/'].append("%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
        
        elif filename[0] == '.': #Hidden - ignore
            pass

        else: #Directory
            self.directories[path] = []
            feed = self.gn.get_docs(folder = filename)
            for file in feed.entry:
                if file.GetDocumentType() == 'folder':
                    self.directories[os.path.join(path, file.title.text.decode(self.codec))] = []
                    self.directories[path].append(file.title.text.decode(self.codec))
                else:
                    self.directories[path].append("%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
        
        for entry in self.directories[path]:
            dirents.append(entry)
        
	if 'My folders' in dirents:
            dirents.remove('My folders')
	
        # Set the appropriate attributes for use with getattr()
        for file in feed.entry:
            p = os.path.join(path, file.title.text.decode(self.codec))
            if file.GetDocumentType() != 'folder':
                p = '%s.%s' % (p, self._file_extension(file))
            self._setattr(path = p, entry = file)

        # Display all hidden files in dirents
        tmp_path = '%s%s' % (self.home, path)
        try:
            os.makedirs(tmp_path.encode(self.codec))
        except OSError:
            pass
        
        if os.path.exists(tmp_path.encode(self.codec)):
            for file in [f for f in os.listdir(tmp_path.encode(self.codec)) if f[0] == '.']:
                dirents.append(file)
                self._setattr(path = os.path.join(tmp_path, file))

        for r in dirents:
            yield fuse.Direntry(r.encode(self.codec))

    def mknod(self, path, mode, dev):
        """
        Purpose: Create file nodes. Use mkdir to create directories
        path: Path of file to create
        mode: Ignored (for now)
        dev: Ignored (for now)
        Returns: 0 to indicate succes
        """
        path = unicode(path, self.codec)
        filename = os.path.basename(path)
        dir = os.path.dirname(path)
        tmp_path = '%s%s' % (self.home, path)
        tmp_dir = '%s%s' % (self.home, dir)
        
        if filename[0] != '.':
            self.to_upload[path] = True
        else:
            try:
                os.makedirs(tmp_dir.encode(self.codec), 0644)
            except OSError:
                pass #Assume that it already exists
            os.mknod(tmp_path.encode(self.codec), 0644)
        self._setattr(path = path)
        self.files[path].set_file_attr(0)
        self.directories[dir].append(filename)
        return 0

    def open(self, path, flags):
        """
        Purpose: Open the file referred to by path
        path: String giving the path to the file to open
        flags: String giving Read/Write/Append Flags to apply to file
        Returns: Pointer to file
        """
        path = unicode(path, self.codec)
        filename = os.path.basename(path)
        tmp_path = '%s%s' % (self.home, path)
        ## I think that's all of them. The others are just different
        ## ways of representing the one defined here
        ## Buffer will just be written to a new temporary file and this
        ## will then be uploaded
        if flags == self.READ:
            f = 'r'
        elif flags == self.WRITE:
            f = 'w'
        elif flags == self.READWRITE:
            f = 'r+'
        elif flags == self.APPEND:
            f = 'a'
        elif flags == self.APPENDRW:
            f = 'a+'
        elif type(f) is str: # Assume that it was passed from self.read()
            f = flags
        else:
            f = 'a+' # Just do something to make it work ;-)
        if not os.path.exists(tmp_path):
            try:
                os.makedirs(os.path.dirname(tmp_path))
            except OSError:
                pass #Assume path exists
            if filename[0] != '.':
                file = self.gn.get_file(path, tmp_path, f)
            else:
                file = open(tmp_path.encode(self.codec), f)
        else:
            file = open(tmp_path.encode(self.codec), f)
                            
        self.files[path].st_size = os.path.getsize(tmp_path.encode(self.codec))
        return file

    def write(self, path, buf, offset, fh = None):
        """
        Purpose: Write the file to Google Docs
        path: Path of the file to write as String
        buf: Data to write to Google Docs
        offset: Ignored (for now)
        fh: File to read
        Returns: 0 to indicate success
        """

        path = unicode(path, self.codec)
        filename = os.path.basename(path)
        tmp_path = '%s%s' % (self.home, path)
        if fh is None:
            fh = open(tmp_path.encode(self.codec), 'wb')
        fh.seek(offset)
        fh.write(buf)
	
        if filename[0] != '.':
            self.written[path] = True
	    self.time_accessed[path] = time.time()
        return len(buf)

    def flush(self, path, fh = None):
        """
        Purpose: Flush the write data and upload it to Google Docs
        path: String containing path to file to flush
        fh: File Handle
        """
        if fh is not None:
            fh.close()

    def unlink(self, path):
        """
        Purpose: Remove a file
        path: String containing relative path to file using mountpoint as /
        """
        path = unicode(path, self.codec)
        filename = os.path.basename(path.encode(self.codec))
        if filename[0] == '.':
            tmp_path = u'%s%s' % (self.home, path)
            if os.path.exists(tmp_path.encode(self.codec)):
                if os.path.isdir(tmp_path.encode(self.codec)):
                    return -errno.EISDIR
                    
                os.remove(tmp_path.encode(self.codec))
                return 0
            else:
                return -errno.ENOENT
        if path in self.directories:
            return -errno.EISDIR
        try:
            self.gn.erase(path)
        except AttributeError, e:
            return -errno.ENOENT

    def read(self, path, size = -1, offset = 0, fh = None):
        """
        Purpose: Read from file pointed to by fh
        path: String Path to file if fh is None
        size: Int Number of bytes to read
        offset: Int Offset to start reading from
        fh: File to read
        Returns: Bytes read
        """
        path = unicode(path, self.codec)
        filename = os.path.basename(path)
        
        if fh is None:
            fh = self.open(path.encode(self.codec), 'rb+')
            
        fh.seek(offset)
        buf = fh.read(size)
        tmp_path = '%s%s' % (self.home, path)
        self.time_accessed[tmp_path] = time.time()
        return buf

    def release(self, path, flags, fh = None):
        """
        Purpose: Called after a file is closed
        path: String containing path to file to be released
        flags: Ignored
        fh: File Handle to be released
        """

        self.release_lock.acquire()
        path = unicode(path, self.codec)
        filename = os.path.basename(path)
        tmp_path = '%s%s' % (self.home, path)

        if path in self.to_upload and path in self.written:
            self.gn.upload_file(tmp_path)
            del self.to_upload[path]
        
        elif os.path.exists(tmp_path):
            if path in self.written:
                self.gn.update_file_contents(path, tmp_path)
                del self.written[path]
            
        for t in self.time_accessed:
            if time.time() - self.time_accessed[t] > 300:
                os.remove(t.encode(self.codec))
        self.release_lock.release()

    def mkdir(self, path, mode):
        """
        Purpose: Make a directory
        path: String containing path to directory to create
        mode: Ignored (for now)
        """
        path = unicode(path, self.codec)
        dir, filename = os.path.split(path)
        tmp_path = '%s%s' % (self.home, path)
        
        if path in self.directories:
            return -errno.EEXIST
        if dir in self.directories:
            self.directories[os.path.dirname(path)].append(filename)
        else:
            return -errno.ENOENT
        
        self.gn.make_folder(path)
        self.directories[path] = []
        self._setattr(path, file = False)
        os.makedirs(tmp_path.encode(self.codec))
        
        return 0

    def rmdir(self, path):
        """
        Purpose: Remove a directory referenced by path
        path: String containing path to directory to remove
        """
        path = unicode(path, self.codec)
        tmp_path = '%s%s' % (self.home, path)
        filename = os.path.basename(path)
        self.readdir(path, 0)
        if path in self.directories:
            if len(self.directories[path]) == 0: #Empty
                self.gn.erase(path, folder = True)
                self.directories[os.path.dirname(path)].remove(filename)
                del self.files[path]
                del self.directories[path]
                os.removedirs(tmp_path.encode(self.codec))
            else:
                return -errno.ENOTEMPTY
        else:
            return -errno.ENOENT
        return 0

    def rename(self, pathfrom, pathto):
        """
        Purpose: Move file to new location. Cannot rename in place.
        pathfrom: String path of file to move
        pathto: String new file path
        """
        
        pathfrom = unicode(pathfrom, self.codec)
        pathto = unicode(pathto, self.codec)
        tmp_path_from = '%s%s' % (self.home, pathfrom)
        tmp_path_to = '%s%s' % (self.home, pathto)
        
        if pathfrom == pathto:
            return -errno.EEXIST
        elif os.path.dirname(pathfrom) == os.path.dirname(pathto):
            return -errno.ESAMEDIR
        else: ## Move the file
            if os.path.exists(tmp_path_from.encode(self.codec)):
                os.rename(tmp_path_from, tmp_path_to)
            if pathfrom in self.directories:
                self.directories[pathto] = self.directories[pathfrom]
                del self.directories[pathfrom]
            self.files[pathto] = self.files[pathfrom]
            del self.files[pathfrom]
            if os.path.basename(pathfrom) in self.directories[os.path.dirname(pathfrom)]:
                self.directories[os.path.dirname(pathfrom)].remove(os.path.basename(pathfrom))
            self.directories[os.path.dirname(pathto)].append(os.path.basename(pathto))
            
            self.gn.move_file(pathfrom, pathto)
            
        return 0

    def truncate(self, path, length, *args, **kwargs):
        path = unicode(path, self.codec)
        filename = os.path.basename(path)
        tmp_path = '%s%s' % (self.home, path)
        fh = open(tmp_path.encode(self.codec), 'r+')
        fh.truncate(length)
        fh.close()
        if filename[0] != '.':
            self.written[path] = True
        self.time_accessed[path] = time.time()
        return 0

    def _setattr(self, path, entry = None, file = True):
        """
        Purpose: Set the getattr information for entry
        path: String path to file
        entry: DocumentListEntry object to extract data from
        file: Boolean set to false if setting attributes of a folder
        """
        
        self.files[path] = GStat()
        if entry:
            if entry.GetDocumentType() != 'folder':
                self.files[path].set_file_attr(len(path))
    
            #Set times
            if entry.lastViewed is None:
                self.files[path].set_access_times(self._time_convert(entry.updated.text.decode(self.codec)),
                                            self._time_convert(entry.published.text.decode(self.codec)))

            else:
                self.files[path].set_access_times(self._time_convert(entry.updated.text.decode(self.codec)),
                                            self._time_convert(entry.published.text.decode(self.codec)),
                                            self._time_convert(entry.lastViewed.text.decode(self.codec)))

        else:
            if file:
                self.files[path].set_file_attr(len(path))
                
    def _time_convert(self, t):
        """
        Purpose: Converts the GData String time to UNIX Time
        t: String representation of GData's time format
        Returns: Integer conversion of t in UNIX Time
        """
        return int(time.mktime(tuple([int(x) for x in (t[:10].split('-')) + t[11:19].split(':')]) + (0,0,0)))

    def _file_extension(self, entry):
        """
        Purpose: Determine the file extension for the given entry
        entry: DocumentListEntry object to scan for filetype
        Returns: String of length 3 with file extension (Currently only Oasis filetypes)
        """

        if entry.GetDocumentType() == 'document':
            return 'doc'
        elif entry.GetDocumentType() == 'spreadsheet':
            return 'xls'
        elif entry.GetDocumentType() == 'presentation':
            return 'ppt'

        #Should never reach this - used for debugging
        return entry.GetDocumentType()

def main():
    """
    Purpose: Mount the filesystem
    Returns: 0 To indicate successful operation
    """

    usage = """Google Docs FS: Mounts Google Docs files on a local
    filesystem gFile.py email password mountpoint""" + fuse.Fuse.fusage

    passwd = None
    while not passwd:
        passwd = getpass.getpass()
    
    #GFile expects things in the reverse order
    sys.argv[1], sys.argv[2] = sys.argv[2], sys.argv[1]
    
    gfs = GFile(sys.argv[1], passwd, version = "%prog " + fuse.__version__,
        usage = usage, dash_s_do='setsingle')
    gfs.parse(errex=1)
    gfs.main()

    return 0

if __name__ == '__main__':
    main()
