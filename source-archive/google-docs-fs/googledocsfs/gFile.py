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
import datetime
import random
import string
import statistics
import csv

from subprocess import *

fuse.fuse_python_api = (0, 2)


class GStat(fuse.Stat):
    """
    The stat class to use for getattr
    """

    def __init__(self):
        """
        Purpose: Sets the attributes to folder attributes
        Returns: Nothing
        """
        self.st_mode = stat.S_IFDIR | 0o744
        self.st_ino = 0
        self.st_dev = 0
        self.st_nlink = 2
        self.st_uid = os.getuid()
        self.st_gid = os.getgid()
        self.st_size = 4096
        self.st_atime = time.time()
        self.st_mtime = self.st_atime
        self.st_ctime = self.st_atime
        self.labels = []
        self.receiveTime = self.st_atime
        self.service_type = "proc"
        self.freshness_per = 0.1
        self.shelf_life = 1

    def set_file_attr(self, size, labels, service_type, freshness_per, shelf_life):
        """
        Purpose: Set attributes of a file
        size: int the file's size in bytes
        TODO: Add labels and all other attributes used in IcarusEdge simulator
        """
        self.st_mode = stat.S_IFREG | 0o744
        self.st_nlink = 1
        self.st_size = size
        self.labels = labels
        self.service_type = service_type
        self.freshness_per = freshness_per
        self.shelf_life = shelf_life

    def set_access_times(self, mtime, ctime, atime=None):
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
        self.home = '%s' % (os.path.expanduser('~'),)
        self.labeled = {}
        self.timings = {}
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

    def getattr(self, path, labels=None):
        """
        Purpose: Get information about a file
        path: String containing relative path to file using mountpoint as /
        Returns: a GStat object with some updated values

        TODO: Main place where you could be looking for file with specific labels
        """

        filename = os.path.basename(path)
        dir = os.path.dirname(path)

        if '/' not in self.files:
            self.files['/'] = GStat()

        # files = self.gn.get_docs(folder = path) # All must be in root folder
        # if files.GetDocumentType() == 'folder':
        #     f = [files]
        #     for label in labels:
        #         if label not in self.files[path].labels:
        #             f.append[self.files[path]]

        if path in self.files:
            st = self.files[path]
        elif filename[0] == '.':
            st = os.stat(('%s%s' % (self.home, path)).encode(self.codec))
        else:
            f = self.gn.get_filename(path, 'true')
            if f is None:
                f = []
                feed = self.gn.get_docs(folder=filename)
                for fi in feed.entry:
                    if all(label in fi.labels for label in labels):
                        f.append(fi)
            self._setattr(path=path, entry=f)
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
        filename = os.path.basename(path)

        if path == '/':  # Root
            excludes = []
            self.directories['/'] = []
            feed = self.gn.get_docs(filetypes=['folder'])
            for dir in feed.entry:
                excludes.append('-' + dir.title.text.decode(self.codec))
                self.directories['%s%s' % (path, dir.title.text.decode(self.codec))] = []
            if len(excludes) > 0:
                i = 0
                while i < len(excludes):
                    excludes[i] = excludes[i].encode(self.codec)
                    i += 1
                feed = self.gn.get_docs(filetypes=excludes)
            else:
                feed = self.gn.get_docs()  # All must be in root folder

            for file in feed.entry:
                if file.GetDocumentType() == 'folder':
                    self.directories['/'].append('%s' % (file.title.text.decode(self.codec),))
                else:
                    self.directories['/'].append(
                        "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))

        elif filename[0] == '.':  # Hidden - ignore
            pass

        else:  # Directory
            self.directories[path] = []
            feed = self.gn.get_docs(folder=filename)
            for file in feed.entry:
                if file.GetDocumentType() == 'folder':
                    self.directories[os.path.join(path, file.title.text.decode(self.codec))] = []
                    self.directories[path].append(file.title.text.decode(self.codec))
                else:
                    self.directories[path].append(
                        "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))

        for entry in self.directories[path]:
            dirents.append(entry)

        if 'My folders' in dirents:
            dirents.remove('My folders')

        # Set the appropriate attributes for use with getattr()
        for file in feed.entry:
            p = os.path.join(path, file.title.text.decode(self.codec))
            if file.GetDocumentType() != 'folder':
                p = '%s.%s' % (p, self._file_extension(file))
            self._setattr(path=p, entry=file)

        # Display all hidden files in dirents
        tmp_path = '%s%s' % (self.home, path)
        try:
            os.makedirs(tmp_path.encode(self.codec))
        except OSError:
            pass

        if os.path.exists(tmp_path.encode(self.codec)):
            for file in [f for f in os.listdir(tmp_path.encode(self.codec)) if f[0] == '.']:
                dirents.append(file)
                self._setattr(path=os.path.join(tmp_path, file))

        for r in dirents:
            yield fuse.Direntry(r.encode(self.codec))

    def readdir_labels(self, path, labels, offset):
        """
        Purpose: Give a listing for ls
        path: String containing relative path to file using mountpoint as /
        offset: Included for compatibility. Does nothing
        Returns: Directory listing for ls
        """
        self.labeled = {}
        dirents = ['.', '..']
        filename = os.path.basename(path)

        if path == '/':  # Root
            excludes = []
            self.directories['/'] = []
            self.labeled['/'] = {}
            # for dir in feed.entry:
            #     excludes.append('-' + dir.title.text.decode(self.codec))
            #     self.directories['%s%s' % (path, dir.title.text.decode(self.codec))] = []
            # if len(excludes) > 0:
            #     i = 0
            #     while i < len(excludes):
            #         excludes[i] = excludes[i].encode(self.codec)
            #         i += 1
            #     feed = self.gn.get_docs(filetypes=excludes)
            # else:
            #     feed = self.gn.get_docs()  # All must be in root folder

            # for file in feed.entry:
            #     if file.GetDocumentType() == 'folder':
            #         self.directories['/'].append('%s' % (file.title.text.decode(self.codec),))
            #     else:
            #
            #         # TODO: Find a way to do the same as above, but filter through files for matching labels
            #
            #         # if path in self.files:
            #         #     self.directories['/'].append(
            #         #         "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
            #         # else:
            #         feed = self.gn.get_docs(folder=filename)
            for fi in self.files:
                f = self.files[fi]
                if all(label in f.labels for label in labels):
                    self.labeled['/'][fi] = f

        elif filename[0] == '.':  # Hidden - ignore
            pass

        else:  # Directory
            self.directories[path] = []
            self.labeled[path] = {}
            # for file in feed.entry:
            #     if file.GetDocumentType() == 'folder':
            #         self.directories[os.path.join(path, file.title.text.decode(self.codec))] = []
            #         self.directories[path].append(file.title.text.decode(self.codec))
            #     else:
            #         # if path in self.files:
            #         #     self.directories[path].append(
            #         #         "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
            #         # else:
            #         feed = self.gn.get_docs(folder=filename)
            for fi in self.files:
                f = self.files[fi]
                if all(label in labels for label in f.labels):
                    self.labeled[path][fi] = f
        return self.labeled

        # for entry in self.directories[path]:
        #     dirents.append(entry)
        #
        # if 'My folders' in dirents:
        #     dirents.remove('My folders')

        # Set the appropriate attributes for use with getattr()
        # for file in feed.entry:
        #     p = os.path.join(path, file.title.text.decode(self.codec))
        #     if file.GetDocumentType() != 'folder':
        #         p = '%s.%s' % (p, self._file_extension(file))
        #     self._setattr(path=p, entry=file, labels=labels)

        # f = []
        # feed = self.gn.get_docs(folder=filename)
        # for fi in feed.entry:
        #     if all(label in fi.labels for label in labels):
        #         self.f.append(
        #             "%s.%s" % (fi.title.text.decode(self.codec), self._file_extension(fi)))
        # self.directories[path].extend(f)
        #
        # # Display all hidden files in dirents
        # tmp_path = '%s%s' % (self.home, path)
        # try:
        #     os.makedirs(tmp_path.encode(self.codec))
        # except OSError:
        #     pass
        #
        # if os.path.exists(tmp_path.encode(self.codec)):
        #     for file in [f for f in os.listdir(tmp_path.encode(self.codec)) if f[0] == '.']:
        #         dirents.append(file)
        #         self._setattr(path=os.path.join(tmp_path, file))
        #
        # for r in dirents:
        #     yield fuse.Direntry(r.encode(self.codec))

        # TODO: ADAPT STRICTLY FOR LABEL LOOKUP, ABOVE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

        # if path in self.files:
        #     st = self.files[path]
        # elif filename[0] == '.':
        #     st = os.stat(('%s%s' % (self.home, path)).encode(self.codec))
        # else:
        #     f = self.gn.get_filename(path, 'true')
        #     if f is None:
        #         f = []
        #         feed = self.gn.get_docs(folder=filename)
        #         for fi in feed.entry:
        #             if all(label in fi.labels for label in labels):
        #                 f.append(fi)
        #     self._setattr(path=path, entry=f)
        #     st = self.files[path]


    def readdir_times(self, path, max_time, min_time, offset):
        """
        Purpose: Give a listing for ls
        path: String containing relative path to file using mountpoint as /
        offset: Included for compatibility. Does nothing
        Returns: Directory listing for ls
        """
        self.timings = {}
        dirents = ['.', '..']
        filename = os.path.basename(path)

        if path == '/':  # Root
            excludes = []
            self.directories['/'] = []
            self.timings['/'] = {}
            # for dir in feed.entry:
            #     excludes.append('-' + dir.title.text.decode(self.codec))
            #     self.directories['%s%s' % (path, dir.title.text.decode(self.codec))] = []
            # if len(excludes) > 0:
            #     i = 0
            #     while i < len(excludes):
            #         excludes[i] = excludes[i].encode(self.codec)
            #         i += 1
            #     feed = self.gn.get_docs(filetypes=excludes)
            # else:
            #     feed = self.gn.get_docs()  # All must be in root folder

            # for file in feed.entry:
            #     if file.GetDocumentType() == 'folder':
            #         self.directories['/'].append('%s' % (file.title.text.decode(self.codec),))
            #     else:
            #
            #         # TODO: Find a way to do the same as above, but filter through files for matching labels
            #
            #         # if path in self.files:
            #         #     self.directories['/'].append(
            #         #         "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
            #         # else:
            #         feed = self.gn.get_docs(folder=filename)
            for fi in self.files:
                f = self.files[fi]
                if min_time <= f.st_mtime <= max_time:
                    self.timings['/'][fi] = f

        elif filename[0] == '.':  # Hidden - ignore
            pass

        else:  # Directory
            self.directories[path] = []
            self.timings[path] = {}
            # for file in feed.entry:
            #     if file.GetDocumentType() == 'folder':
            #         self.directories[os.path.join(path, file.title.text.decode(self.codec))] = []
            #         self.directories[path].append(file.title.text.decode(self.codec))
            #     else:
            #         # if path in self.files:
            #         #     self.directories[path].append(
            #         #         "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
            #         # else:
            #         feed = self.gn.get_docs(folder=filename)
            for fi in self.files:
                f = self.files[fi]
                if min_time <= f.st_mtime <= max_time:
                    self.timings[path][fi] = f
        return self.timings

        # for entry in self.directories[path]:
        #     dirents.append(entry)
        #
        # if 'My folders' in dirents:
        #     dirents.remove('My folders')

        # Set the appropriate attributes for use with getattr()
        # for file in feed.entry:
        #     p = os.path.join(path, file.title.text.decode(self.codec))
        #     if file.GetDocumentType() != 'folder':
        #         p = '%s.%s' % (p, self._file_extension(file))
        #     self._setattr(path=p, entry=file, labels=labels)

        # f = []
        # feed = self.gn.get_docs(folder=filename)
        # for fi in feed.entry:
        #     if all(label in fi.labels for label in labels):
        #         self.f.append(
        #             "%s.%s" % (fi.title.text.decode(self.codec), self._file_extension(fi)))
        # self.directories[path].extend(f)
        #
        # # Display all hidden files in dirents
        # tmp_path = '%s%s' % (self.home, path)
        # try:
        #     os.makedirs(tmp_path.encode(self.codec))
        # except OSError:
        #     pass
        #
        # if os.path.exists(tmp_path.encode(self.codec)):
        #     for file in [f for f in os.listdir(tmp_path.encode(self.codec)) if f[0] == '.']:
        #         dirents.append(file)
        #         self._setattr(path=os.path.join(tmp_path, file))
        #
        # for r in dirents:
        #     yield fuse.Direntry(r.encode(self.codec))

        # TODO: ADAPT STRICTLY FOR LABEL LOOKUP, ABOVE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

        # if path in self.files:
        #     st = self.files[path]
        # elif filename[0] == '.':
        #     st = os.stat(('%s%s' % (self.home, path)).encode(self.codec))
        # else:
        #     f = self.gn.get_filename(path, 'true')
        #     if f is None:
        #         f = []
        #         feed = self.gn.get_docs(folder=filename)
        #         for fi in feed.entry:
        #             if all(label in fi.labels for label in labels):
        #                 f.append(fi)
        #     self._setattr(path=path, entry=f)
        #     st = self.files[path]
    
    
    def readdir_times_labels(self, path, max_time, min_time, labels, offset):
        """
        Purpose: Give a listing for ls
        path: String containing relative path to file using mountpoint as /
        offset: Included for compatibility. Does nothing
        Returns: Directory listing for ls
        """
        self.labeled_timings = {}
        dirents = ['.', '..']
        filename = os.path.basename(path)

        if path == '/':  # Root
            excludes = []
            self.directories['/'] = []
            self.labeled_timings['/'] = {}
            # for dir in feed.entry:
            #     excludes.append('-' + dir.title.text.decode(self.codec))
            #     self.directories['%s%s' % (path, dir.title.text.decode(self.codec))] = []
            # if len(excludes) > 0:
            #     i = 0
            #     while i < len(excludes):
            #         excludes[i] = excludes[i].encode(self.codec)
            #         i += 1
            #     feed = self.gn.get_docs(filetypes=excludes)
            # else:
            #     feed = self.gn.get_docs()  # All must be in root folder

            # for file in feed.entry:
            #     if file.GetDocumentType() == 'folder':
            #         self.directories['/'].append('%s' % (file.title.text.decode(self.codec),))
            #     else:
            #
            #         # TODO: Find a way to do the same as above, but filter through files for matching labels
            #
            #         # if path in self.files:
            #         #     self.directories['/'].append(
            #         #         "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
            #         # else:
            #         feed = self.gn.get_docs(folder=filename)
            for fi in self.files:
                f = self.files[fi]
                if min_time <= f.st_mtime <= max_time and all(label in f.labels for label in labels):
                        self.labeled_timings['/'][fi] = f

        elif filename[0] == '.':  # Hidden - ignore
            pass

        else:  # Directory
            self.directories[path] = []
            self.labeled_timings[path] = {}
            # for file in feed.entry:
            #     if file.GetDocumentType() == 'folder':
            #         self.directories[os.path.join(path, file.title.text.decode(self.codec))] = []
            #         self.directories[path].append(file.title.text.decode(self.codec))
            #     else:
            #         # if path in self.files:
            #         #     self.directories[path].append(
            #         #         "%s.%s" % (file.title.text.decode(self.codec), self._file_extension(file)))
            #         # else:
            #         feed = self.gn.get_docs(folder=filename)
            for fi in self.files:
                f = self.files[fi]
                if min_time <= f.st_mtime <= max_time and all(label in f.labels for label in labels):
                    self.labeled_timings[path][fi] = f
        return self.labeled_timings

        # for entry in self.directories[path]:
        #     dirents.append(entry)
        #
        # if 'My folders' in dirents:
        #     dirents.remove('My folders')

        # Set the appropriate attributes for use with getattr()
        # for file in feed.entry:
        #     p = os.path.join(path, file.title.text.decode(self.codec))
        #     if file.GetDocumentType() != 'folder':
        #         p = '%s.%s' % (p, self._file_extension(file))
        #     self._setattr(path=p, entry=file, labels=labels)

        # f = []
        # feed = self.gn.get_docs(folder=filename)
        # for fi in feed.entry:
        #     if all(label in fi.labels for label in labels):
        #         self.f.append(
        #             "%s.%s" % (fi.title.text.decode(self.codec), self._file_extension(fi)))
        # self.directories[path].extend(f)
        #
        # # Display all hidden files in dirents
        # tmp_path = '%s%s' % (self.home, path)
        # try:
        #     os.makedirs(tmp_path.encode(self.codec))
        # except OSError:
        #     pass
        #
        # if os.path.exists(tmp_path.encode(self.codec)):
        #     for file in [f for f in os.listdir(tmp_path.encode(self.codec)) if f[0] == '.']:
        #         dirents.append(file)
        #         self._setattr(path=os.path.join(tmp_path, file))
        #
        # for r in dirents:
        #     yield fuse.Direntry(r.encode(self.codec))

        # TODO: ADAPT STRICTLY FOR LABEL LOOKUP, ABOVE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

        # if path in self.files:
        #     st = self.files[path]
        # elif filename[0] == '.':
        #     st = os.stat(('%s%s' % (self.home, path)).encode(self.codec))
        # else:
        #     f = self.gn.get_filename(path, 'true')
        #     if f is None:
        #         f = []
        #         feed = self.gn.get_docs(folder=filename)
        #         for fi in feed.entry:
        #             if all(label in fi.labels for label in labels):
        #                 f.append(fi)
        #     self._setattr(path=path, entry=f)
        #     st = self.files[path]


    def mknod(self, path, labels=None, service_type='proc', freshness_per=0.1, shelf_life=1, mode=None, dev=None):
        """
        Purpose: Create file nodes. Use mkdir to create directories
        path: Path of file to create
        mode: Ignored (for now)
        dev: Ignored (for now)
        Returns: 0 to indicate succes
        """
        if labels is None:
            labels = []
        filename = os.path.basename(path)
        dir = os.path.dirname(path)
        tmp_path = '%s%s' % (self.home, path)
        tmp_dir = '%s%s' % (self.home, dir)

        if filename[0] != '.':
            self.to_upload[path] = True
        else:
            try:
                os.makedirs(tmp_dir.encode(self.codec), 0o644)
            except OSError:
                pass  # Assume that it already exists
            os.mknod(tmp_path.encode(self.codec), 0o644)
        self._setattr(path=path, labels=labels, service_type=service_type, freshness_per=freshness_per,
                      shelf_life=shelf_life)
        self.files[path].set_file_attr(0, labels, service_type, freshness_per, shelf_life)
        if self.directories.has_key(dir):
            self.directories[dir].append(filename)
        else:
            self.directories[dir] = [filename]
        return 0

    def open(self, path, flags):
        """
        Purpose: Open the file referred to by path
        path: String giving the path to the file to open
        flags: String giving Read/Write/Append Flags to apply to file
        Returns: Pointer to file
        """
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
        elif type(flags) is str:  # Assume that it was passed from self.read()
            f = flags
        else:
            f = 'a+'  # Just do something to make it work ;-)
        if not os.path.exists(tmp_path):
            try:
                os.makedirs(os.path.dirname(tmp_path))
            except OSError:
                pass  # Assume path exists
            if filename[0] != '.':
                file = self.gn.get_file(path, tmp_path, f)
            else:
                file = open(tmp_path.encode(self.codec), f)
        else:
            file = open(tmp_path.encode(self.codec), f)

        self.files[path].st_size = os.path.getsize(tmp_path.encode(self.codec))
        return file

    def write(self, path, buf, offset, fh=None):
        """
        Purpose: Write the file to Google Docs
        path: Path of the file to write as String
        buf: Data to write to Google Docs
        offset: Ignored (for now)
        fh: File to read
        Returns: 0 to indicate success
        """

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

    def flush(self, path, fh=None):
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
        except AttributeError as e:
            return -errno.ENOENT

    def read(self, path, size=-1, offset=0, fh=None):
        """
        Purpose: Read from file pointed to by fh
        path: String Path to file if fh is None
        size: Int Number of bytes to read
        offset: Int Offset to start reading from
        fh: File to read
        Returns: Bytes read
        """
        filename = os.path.basename(path)

        if fh is None:
            fh = self.open(path.encode(self.codec), 'rb+')

        fh.seek(offset)
        buf = fh.read(size)
        tmp_path = '%s%s' % (self.home, path)
        self.time_accessed[tmp_path] = time.time()
        return buf

    def release(self, path, flags, fh=None):
        """
        Purpose: Called after a file is closed
        path: String containing path to file to be released
        flags: Ignored
        fh: File Handle to be released
        """

        self.release_lock.acquire()
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
        self._setattr(path, file=False)
        os.makedirs(tmp_path.encode(self.codec))

        return 0

    def rmdir(self, path):
        """
        Purpose: Remove a directory referenced by path
        path: String containing path to directory to remove
        """
        tmp_path = '%s%s' % (self.home, path)
        filename = os.path.basename(path)
        self.readdir(path, 0)
        if path in self.directories:
            if len(self.directories[path]) == 0:  # Empty
                self.gn.erase(path, folder=True)
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

        tmp_path_from = '%s%s' % (self.home, pathfrom)
        tmp_path_to = '%s%s' % (self.home, pathto)

        if pathfrom == pathto:
            return -errno.EEXIST
        elif os.path.dirname(pathfrom) == os.path.dirname(pathto):
            return -errno.ESAMEDIR
        else:  ## Move the file
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
        filename = os.path.basename(path)
        tmp_path = '%s%s' % (self.home, path)
        fh = open(tmp_path.encode(self.codec), 'r+')
        fh.truncate(length)
        fh.close()
        if filename[0] != '.':
            self.written[path] = True
        self.time_accessed[path] = time.time()
        return 0

    def _setattr(self, path, entry=None, file=True, labels=None, service_type='proc', freshness_per=0.1, shelf_life=1):
        """
        Purpose: Set the getattr information for entry
        path: String path to file
        entry: DocumentListEntry object to extract data from
        file: Boolean set to false if setting attributes of a folder
        """

        if labels is None:
            labels = []
        self.files[path] = GStat()
        if entry:
            if entry.GetDocumentType() != 'folder':
                self.files[path].set_file_attr(len(path), labels, service_type, freshness_per, shelf_life)

            # Set times
            if entry.lastViewed is None:
                self.files[path].set_access_times(self._time_convert(entry.updated.text.decode(self.codec)),
                                                  self._time_convert(entry.published.text.decode(self.codec)))

            else:
                self.files[path].set_access_times(self._time_convert(entry.updated.text.decode(self.codec)),
                                                  self._time_convert(entry.published.text.decode(self.codec)),
                                                  self._time_convert(entry.lastViewed.text.decode(self.codec)))

        else:
            if file:
                self.files[path].set_file_attr(len(path), labels, service_type, freshness_per, shelf_life)

    def _time_convert(self, t):
        """
        Purpose: Converts the GData String time to UNIX Time
        t: String representation of GData's time format
        Returns: Integer conversion of t in UNIX Time
        """
        return int(time.mktime(tuple([int(x) for x in (t[:10].split('-')) + t[11:19].split(':')]) + (0, 0, 0)))

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

        # Should never reach this - used for debugging
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

    # GFile expects things in the reverse order
    # sys.argv[1], sys.argv[2] = sys.argv[2], sys.argv[1]

    gfs = GFile(sys.argv[0], passwd, version="%prog " + fuse.__version__,
                usage=usage, dash_s_do='setsingle')
    gfs.parse(errex=1)

    # TODO: Get files generated and looked up, getting some time stamps for all

    # gfs.mknod('/file.doc', ['traffic', 'value'], 'non-proc')
    # gfs.mknod('/file1.doc', ['IoT', 'result'], 'non-proc')
    #
    # gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/file', 'hello', 0)
    #
    # gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/file1', 'hello there', 0)
    #
    # result = gfs.readdir_labels('/', ['traffic', 'value'], None)
    #
    # print result

    # gfs.main()

    # Generating labels
    labels = []
    for i in range(0, 10):
        label = ''.join(random.SystemRandom().choice(string.ascii_letters) for _ in range(4))
        labels.append(label)

    # Generating image-based files
    # TODO: Write bytecode images in doc files:
    os.chdir("/home/chrisys/Repos_google_fs/images")
    i = 0
    gfs.mknod('/logwrite10.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/logwrite10.doc', 'log_write start:\n', 0)
    log_write = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/logwrite10.doc', "a")
    gfs.mknod('/loglookup10.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/loglookup10.doc', 'log_lookup start:\n', 0)
    log_lookup = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/loglookup10.doc', "a")
    for filename in os.listdir(os.getcwd()):
        with open(filename, "rb") as image:
            f = image.read()
            b = bytearray(f)
        l = []
        for j in range(0, 4):
            l.append(random.SystemRandom().choice(labels))

        i += 1
        if i % 5000 == 0:
            wres_time = []
            for iter in range(0, 5):
                l = []
                for j in range(0, 4):
                    l.append(random.SystemRandom().choice(labels))
                gfs.mknod('/' + filename, l)
                write_time = datetime.datetime.now()
                gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/'+filename, b, 0)
                wrote_time = datetime.datetime.now()
                wres_time.append((wrote_time - write_time).microseconds)
                written_delay = statistics.mean(wres_time)
                log_write.write( str(written_delay) + '\n')
                # str(written_delay) + ' microseconds writing time - the file was written at: '+ str(wrote_time
            i += 5

            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', random.SystemRandom().choice(labels), None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))
                # la + " has " + str(n) + " matching labelled files."

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            l = []
            for i in range(0, 1):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            l = []
            for i in range(0, 2):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')


            l = []
            for i in range(0, 3):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

        else:
            gfs.mknod('/' + filename, l)
            gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/'+filename, b, 0)

    log_write.close()
    log_lookup.close()



    # Generating labels
    labels = []
    for i in range(0, 100):
        label = ''.join(random.SystemRandom().choice(string.ascii_letters) for _ in range(4))
        labels.append(label)

    # Generating image-based files
    # TODO: Write bytecode images in doc files:
    os.chdir("/home/chrisys/Repos_google_fs/images")
    i = 0
    gfs.mknod('/logwrite100.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/logwrite100.doc', 'log_write start:\n', 0)
    log_write = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/logwrite100.doc', "a")
    gfs.mknod('/loglookup100.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/loglookup100.doc', 'log_lookup start:\n', 0)
    log_lookup = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/loglookup100.doc', "a")
    for filename in os.listdir(os.getcwd()):
        with open(filename, "rb") as image:
            f = image.read()
            b = bytearray(f)
        l = []
        for j in range(0, 4):
            l.append(random.SystemRandom().choice(labels))

        i += 1
        if i % 5000 == 0:
            wres_time = []
            for iter in range(0, 5):
                l = []
                for j in range(0, 4):
                    l.append(random.SystemRandom().choice(labels))
                gfs.mknod('/' + filename, l)
                write_time = datetime.datetime.now()
                gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/'+filename, b, 0)
                wrote_time = datetime.datetime.now()
                wres_time.append((wrote_time - write_time).microseconds)
                written_delay = statistics.mean(wres_time)
                log_write.write( str(written_delay) + '\n')
            i += 5

            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', random.SystemRandom().choice(labels), None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            l = []
            for i in range(0, 1):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write(str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            l = []
            for i in range(0, 2):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')


            l = []
            for i in range(0, 3):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

        else:
            gfs.mknod('/' + filename, l)
            gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/'+filename, b, 0)

    log_write.close()
    log_lookup.close()



    # Generating labels
    labels = []
    for i in range(0, 1000):
        label = ''.join(random.SystemRandom().choice(string.ascii_letters) for _ in range(4))
        labels.append(label)

    # Generating image-based files
    # TODO: Write bytecode images in doc files:
    os.chdir("/home/chrisys/Repos_google_fs/images")
    i = 0
    gfs.mknod('/logwrite1000.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/logwrite1000.doc', 'log_write start:\n', 0)
    log_write = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/logwrite1000.doc', "a")
    gfs.mknod('/loglookup1000.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/loglookup1000.doc', 'log_lookup start:\n', 0)
    log_lookup = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/loglookup1000.doc', "a")
    for filename in os.listdir(os.getcwd()):
        with open(filename, "rb") as image:
            f = image.read()
            b = bytearray(f)
        l = []
        for j in range(0, 4):
            l.append(random.SystemRandom().choice(labels))

        i += 1
        if i % 5000 == 0:
            wres_time = []
            for iter in range(0, 5):
                l = []
                for j in range(0, 4):
                    l.append(random.SystemRandom().choice(labels))
                gfs.mknod('/' + filename, l)
                write_time = datetime.datetime.now()
                gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/'+filename, b, 0)
                wrote_time = datetime.datetime.now()
                wres_time.append((wrote_time - write_time).microseconds)
                written_delay = statistics.mean(wres_time)
                log_write.write( str(written_delay) + '\n')
            i += 5

            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', random.SystemRandom().choice(labels), None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            l = []
            for i in range(0, 1):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            l = []
            for i in range(0, 2):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')


            l = []
            for i in range(0, 3):
                l.append(random.SystemRandom().choice(labels))
            lookup_time = datetime.datetime.now()
            result = gfs.readdir_labels('/', l, None)
            res_time = datetime.datetime.now()
            for la in result:
                n = 0
                for j in result[la]:
                    n += 1
                log_lookup.write(str(n))

            lookup_delay = res_time - lookup_time
            log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

        else:
            gfs.mknod('/' + filename, l)
            gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/'+filename, b, 0)

    log_write.close()
    log_lookup.close()

    # TODO: Check each 5000 file writes, for write and lookup speed, and at the end, for each label lookup speed.






    # IoT Use Cases

    # Times of creation
    gen_times = []

    # generating messages (files), with a specific time frame in time (1-2 minutes plus/minus from NOW)

    # TODO: Write bytecode images in doc files:
    os.chdir("/home/chrisys/Repos_google_fs/")
    i = 0
    gfs.mknod('/log_writetimings.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_writetimings.doc', 'log_write start:\n', 0)
    log_write = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_writetimings.doc', "a")
    gfs.mknod('/log_lookuptimings.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_lookuptimings.doc', 'log_lookup start:\n', 0)
    log_lookup = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_lookuptimings.doc', "a")

    # Generate files from IoTFlows row entries
    with open(os.getcwd()+'/flows.csv') as IoTFlows:
        readIoT = csv.reader(IoTFlows, delimiter=',')
        next(readIoT)
        for row in readIoT:
            # File name made up of the device MAC address and the last 6 digits of the time of generation
            gen_times.append(row[3])

            i += 1
            if i % 5000 == 0:
                wres_time = []
                for iter in range(0, 5):
                    gfs.mknod('/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc')
                    write_time = datetime.datetime.now()
                    gfs.files['/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc'].set_access_times(row[3], row[3])
                    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', str(row[9]) + ' ' + str(row[10]) + ' ' + str(row[11]) + ' ' + str(row[12]) + ' ' + str(row[13]), 0)
                    wrote_time = datetime.datetime.now()
                    wres_time.append((wrote_time - write_time).microseconds)
                    written_delay = statistics.mean(wres_time)
                    log_write.write( str(written_delay) + '\n')
                    gen_times.append(row[3])
                    row = next(readIoT)
                i += 5


                time_min = random.SystemRandom().choice(gen_times)
                n = 0
                index = 0
                found = False
                for tmp_time in gen_times:
                    n +=1
                    if tmp_time == time_min:
                        index = n
                time_max = random.SystemRandom().choice(gen_times[index:])

                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times('/', time_max, time_min, None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(la + ", " + str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write(str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            else:
                gfs.mknod('/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc')
                gfs.files['/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc'].set_access_times(row[3], row[3])
                gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', str(row[9]) + ' ' + str(row[10]) + ' ' + str(row[11]) + ' ' + str(row[12]) + ' ' + str(row[13]), 0)

        log_write.close()
        log_lookup.close()



    # Generating labels
    labels = []
    for i in range(0, 100):
        label = ''.join(random.SystemRandom().choice(string.ascii_letters) for _ in range(4))
        labels.append(label)

    # Times of creation
    gen_times = []

    # generating messages (files), with a specific time frame in time (1-2 minutes plus/minus from NOW)

    # TODO: Write bytecode images in doc files:
    os.chdir("/home/chrisys/Repos_google_fs/")
    i = 0
    gfs.mknod('/log_writeIoT100.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_writeIoT100.doc', 'log_write start:\n', 0)
    log_write = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_writeIoT100.doc', "a")
    gfs.mknod('/log_lookupIoT100.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_lookupIoT100.doc', 'log_lookup start:\n', 0)
    log_lookup = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_lookupIoT100.doc', "a")

    # Generate files from IoTFlows row entries
    with open(os.getcwd()+'/flows.csv') as IoTFlows:
        readIoT = csv.reader(IoTFlows, delimiter=',')
        next(readIoT)
        for row in readIoT:
            # File name made up of the device MAC address and the last 6 digits of the time of generation
            gen_times.append(row[3])
            l = []
            for j in range(0, 4):
                l.append(random.SystemRandom().choice(labels))

            i += 1
            if i % 5000 == 0:
                wres_time = []
                for iter in range(0, 5):
                    l = []
                    for j in range(0, 4):
                        l.append(random.SystemRandom().choice(labels))
                    gfs.mknod('/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', l)
                    write_time = datetime.datetime.now()
                    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', str(row[9]) + ' ' + str(row[10]) + ' ' + str(row[11]) + ' ' + str(row[12]) + ' ' + str(row[13]), 0)
                    wrote_time = datetime.datetime.now()
                    wres_time.append((wrote_time - write_time).microseconds)
                    written_delay = statistics.mean(wres_time)
                    log_write.write( str(written_delay) + '\n')
                i += 5

                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/', time_max, time_min, random.SystemRandom().choice(labels), None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

                l = []
                for i in range(0, 1):
                    l.append(random.SystemRandom().choice(labels))
                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/', time_max, time_min, l, None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

                l = []
                for i in range(0, 2):
                    l.append(random.SystemRandom().choice(labels))
                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/', time_max, time_min, l, None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')


                l = []
                for i in range(0, 3):
                    l.append(random.SystemRandom().choice(labels))
                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/', time_max, time_min, l, None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            else:
                gfs.mknod('/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc')
                gfs.files['/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc'].set_access_times(row[3], row[3])
                gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', str(row[9]) + ' ' + str(row[10]) + ' ' + str(row[11]) + ' ' + str(row[12]) + ' ' + str(row[13]), 0)

        log_write.close()
        log_lookup.close()




    # Generating labels
    labels = []
    for i in range(0, 1000):
        label = ''.join(random.SystemRandom().choice(string.ascii_letters) for _ in range(4))
        labels.append(label)

    # Times of creation
    gen_times = []

    # generating messages (files), with a specific time frame in time (1-2 minutes plus/minus from NOW)

    # TODO: Write bytecode images in doc files:
    os.chdir("/home/chrisys/Repos_google_fs/")
    i = 0
    gfs.mknod('/log_writeIoTimings100.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_writeIoTimings100.doc', 'log_write start:\n', 0)
    log_write = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_writeIoTimings100.doc', "a")
    gfs.mknod('/log_lookupIoTimimgs100.doc')
    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_lookupIoTimimgs100.doc', 'log_lookup start:\n', 0)
    log_lookup = open('%s' % (os.path.expanduser('~'),) + '/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/log_lookupIoTimimgs100.doc', "a")

    # Generate files from IoTFlows row entries
    with open(os.getcwd()+'/flows.csv') as IoTFlows:
        readIoT = csv.reader(IoTFlows, delimiter=',')
        next(readIoT)
        for row in readIoT:
            # File name made up of the device MAC address and the last 6 digits of the time of generation
            gen_times.append(row[3])
            l = []
            for j in range(0, 4):
                l.append(random.SystemRandom().choice(labels))

            i += 1
            if i % 5000 == 0:
                wres_time = []
                for iter in range(0, 5):
                    l = []
                    for j in range(0, 4):
                        l.append(random.SystemRandom().choice(labels))
                    gfs.mknod('/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', l)
                    write_time = datetime.datetime.now()
                    gfs.files['/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc'].set_access_times(row[3], row[3])
                    gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', str(row[9]) + ' ' + str(row[10]) + ' ' + str(row[11]) + ' ' + str(row[12]) + ' ' + str(row[13]), 0)
                    wrote_time = datetime.datetime.now()
                    wres_time.append((wrote_time - write_time).microseconds)
                    written_delay = statistics.mean(wres_time)
                    log_write.write( str(written_delay) + '\n')
                    gen_times.append(row[3])
                    row = next(readIoT)
                i += 5

                time_min = random.SystemRandom().choice(gen_times)
                n = 0
                index = 0
                found = False
                for tmp_time in gen_times:
                    n += 1
                    if tmp_time == time_min:
                        index = n
                time_max = random.SystemRandom().choice(gen_times[index:])

                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/', time_max, time_min, random.SystemRandom().choice(labels), None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

                l = []
                for i in range(0, 1):
                    l.append(random.SystemRandom().choice(labels))

                time_min = random.SystemRandom().choice(gen_times)
                n = 0
                index = 0
                found = False
                for tmp_time in gen_times:
                    n += 1
                    if tmp_time == time_min:
                        index = n
                time_max = random.SystemRandom().choice(gen_times[index:])

                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/', time_max, time_min, l, None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

                l = []
                for i in range(0, 2):
                    l.append(random.SystemRandom().choice(labels))

                time_min = random.SystemRandom().choice(gen_times)
                n = 0
                index = 0
                found = False
                for tmp_time in gen_times:
                    n += 1
                    if tmp_time == time_min:
                        index = n
                time_max = random.SystemRandom().choice(gen_times[index:])

                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/', time_max, time_min, l, None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')


                l = []
                for i in range(0, 3):
                    l.append(random.SystemRandom().choice(labels))

                time_min = random.SystemRandom().choice(gen_times)
                n = 0
                index = 0
                found = False
                for tmp_time in gen_times:
                    n += 1
                    if tmp_time == time_min:
                        index = n
                time_max = random.SystemRandom().choice(gen_times[index:])

                lookup_time = datetime.datetime.now()
                result = gfs.readdir_times_labels('/',time_max, time_max, l, None)
                res_time = datetime.datetime.now()
                for la in result:
                    n = 0
                    for j in result[la]:
                        n += 1
                    log_lookup.write(str(n))

                lookup_delay = res_time - lookup_time
                log_lookup.write( str(lookup_delay.seconds) + ':' + str(lookup_delay.microseconds) + '\n')

            else:
                gfs.mknod('/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc')
                gfs.files['/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc'].set_access_times(row[3], row[3])
                gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/' + str(row[0]) + '_' + str(row[3])[-6:] + '.doc', str(row[9]) + ' ' + str(row[10]) + ' ' + str(row[11]) + ' ' + str(row[12]) + ' ' + str(row[13]), 0)

    log_write.close()
    log_lookup.close()

    # gfs.mknod('/file.doc', ['traffic', 'value'], 'non-proc')
    # gfs.mknod('/file1.doc', ['IoT', 'result'], 'non-proc')
    # gfs.mknod('/file2.doc', ['traffic', 'value', 'photo'], 'non-proc')
    #
    # gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/file', 'hello', 0)
    #
    # gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/file1', 'hello there', 0)
    #
    # gfs.write('/Repos_google_fs/source-archive/google-docs-fs/googledocsfs/mntpnt1/file2', 'hello there', 0)
    #
    #
    #
    # lookup_time = datetime.datetime.now()
    # result = gfs.readdir_labels('/', ['traffic', 'value'], None)
    # res_time = datetime.datetime.now()
    # for i in result:
    #     n = 0
    #     for j in result[i]:
    #         n += 1
    #     print i, " has " + str(n) + " matching labelled files."
    #
    # lookup_delay = res_time - lookup_time
    # print(lookup_delay.seconds, ":", lookup_delay.microseconds)

    return 0


if __name__ == '__main__':
    main()
