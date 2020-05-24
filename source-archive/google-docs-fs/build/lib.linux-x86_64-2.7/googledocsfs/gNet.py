#!/usr/bin/env python
#
#   gNet.py
#
#   Copyright 2009 Scott C. Walton <d38dm8nw81k1ng@gmail.com>
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

import os
import gdata.docs.service
import gdata.docs
from gdata import MediaSource

class GNet(object):
    """
    Performs all the main interfacing with Google Docs server as well
    as storing the user's session data
    """

    def __init__(self, em, pw):
        """
        Purpose: Login to Google Docs and store the session cookie
        em: A String containing the user's email address
        pw: A String containing the user's password
        Returns: A GNet object for accessing the GData Docs
        """

        self.gd_client = gdata.docs.service.DocsService()
        self.gd_client.email = em
        self.gd_client.password = pw
        self.gd_client.source = 'google-docs-fs'
        self.gd_client.ssl = True
        self.gd_client.ProgrammaticLogin()
        self.codec = 'utf-8'


    def get_docs(self, filetypes = None, folder = None):
        """
        Purpose: Retrieve a list of all documents
        filetypes: A List containing the filetypes to query
        folder: A String containing the folder to search in
        Returns: A List of documents specified by filetypes: Type gdata.docs.DocumentListFeed
        """
        query = gdata.docs.service.DocumentQuery(categories = filetypes)
        query['showfolders'] = 'true'

        if folder is not None:
            query.AddNamedFolder(self.gd_client.email, folder.encode(self.codec))

        return self.gd_client.Query(query.ToUri())

    def get_filename(self, path, showfolders = 'false'):
        """
        Purpose: Retrieves the file referred to by path from Google
        path: A String containing the path elements of the file
        showfolders: Either 'true' or 'false' - whether get_filename
                     should also retrieve folders (default: 'false')
        Returns: The gdata List Entry object containing the file or None if none exists
        """
        name = os.path.basename(path)
        title = os.path.splitext(name)[0]
        pe = path.split('/')
        query = gdata.docs.service.DocumentQuery()
        query['title'] = title.encode(self.codec)
        query['title-exact'] = 'true'
        query['showfolders'] = showfolders

        feed = self.gd_client.Query(query.ToUri())
        filetype_filter = []
     
        # Filter out any files that don't match the case
        for f in feed.entry:
            if f.title.text.decode(self.codec) == title:
                filetype_filter.append(f)
        # Return the first file encountered in the folder
        # Fix this to be more precise in the final version
        # Need to implement file extensions, then I should be able to
        # check those to get the filetype and a more accurate file
        # May also need to go through the entire file hierarchy to
        # ensure the integrity of the path. May be slower but will be
        # essential to ensure the user doesnt unwittingly erase a
        # random file stored elsewhere
        if len(filetype_filter) == 1: ## Assume it is the correct one
            return filetype_filter[0]
        for entry in filetype_filter:
            ## Assume that if there's only 1 then it's the correct one.
            if os.path.dirname(path) == '/' or len(entry.category) is 1:
                return entry
            ## This doesn't seem to work any more
            for c in entry.category:
                if pe[-2].encode(self.codec) in c.label:
                    return entry
        
    def erase(self, path, folder = False):
        """
        Purpose: Erase a file
        path: String containing path to the file to erase
        """
        if folder is True:
            file = self.get_filename(path, showfolders = 'true')
        else:
            file = self.get_filename(path)
        self.gd_client.Delete(file.GetEditLink().href)

    def upload_file(self, path):
        """
        Purpose: Uploads a file to Google Docs
        path: String containing path of the file to be uploaded
        """
        mime = gdata.docs.service.SUPPORTED_FILETYPES[path[-3:].upper()]
        filename = os.path.basename(path)
        title = filename[:-4]
        dir = os.path.dirname(path)
        
        media = MediaSource(file_path = path.encode(self.codec), content_type = mime)

        if mime in ['CSV', 'ODS', 'XLS']:
            entry = self.gd_client.UploadSpreadsheet(media, title)
        if mime in ['PPT', 'PPS']:
            entry = self.gd_client.UploadPresentation(media, title)
        else:
            entry = self.gd_client.UploadDocument(media, title)

        if dir != '/':
            type = entry.GetDocumentType()
            entry_to = self.get_filename(os.path.basename(dir), showfolders = 'true')

            if type == 'document':
                self.gd_client.MoveDocumentIntoFolder(entry, entry_to)
            elif type == 'spreadsheet':
                self.gd_client.MoveSpreadsheetIntoFolder(entry, entry_to)
            elif type == 'presentation':
                self.gd_client.MovePresentationIntoFolder(entry, entry_to)

    def create_dir(self, path):
        """
        Purpose: Create a directory referred to by path
        path: A list containing the path to the directory to be created
        """

        #Check if folder is in root
        if len(path) > 1:
            parent_dir = path[-2]
        else:
            parent_dir = None

        if parent_dir is None:
            self.gd_client.CreateFolder(path[-1])
        else:
            parent_entry = self.get_filename(parent_dir, showfolders = 'true')
            self.gd_client.CreateFolder(path[-1], parent_entry)

    def get_file(self, path, tmp_path, flags):
        """
        Purpose: Get the file referred to by path off Google Docs.
        path: A string containing the path to the file to download
        flags: A string giving the flags to open the file with
        Returns: The file requested, or -1 if the file doesn't exist
        """

        filename = os.path.basename(path)
        doc = self.get_filename(path)
        
        ## If doc is a new file
        if doc is None:
            import stat
            os.mknod(tmp_path.encode(self.codec), 0700 | stat.S_IFREG)
            return open(tmp_path.encode(self.codec), flags)

        filetype = doc.GetDocumentType()
        if filetype == 'spreadsheet':
            import gdata.spreadsheet.service

            spreadsheets_client = gdata.spreadsheet.service.SpreadsheetsService()
            spreadsheets_client.ClientLogin(self.gd_client.email, self.gd_client.password)
            # substitute the spreadsheets token into our gd_client
            docs_auth_token = self.gd_client.GetClientLoginToken()
            self.gd_client.SetClientLoginToken(spreadsheets_client.GetClientLoginToken())
            self.gd_client.Export(doc.resourceId.text, tmp_path.encode(self.codec))
            self.gd_client.SetClientLoginToken(docs_auth_token)

        else:
            print doc.resourceId.text
            self.gd_client.Export(doc.resourceId.text, tmp_path.encode(self.codec))

        return open(tmp_path.encode(self.codec), flags)

    def update_file_contents(self, path, tmp_path):
        """
        Purpose: Update the contents of the file specified by path
        path: String containing path to file to update
        """
        mime = gdata.docs.service.SUPPORTED_FILETYPES[path[-3:].upper()]
        ms = gdata.MediaSource(file_path = tmp_path.encode(self.codec), content_type = mime)
        entry = self.get_filename(path)
        self.gd_client.Put(data = entry, uri = entry.GetEditMediaLink().href, media_source = ms)

    def make_folder(self, path):
        """
        Purpose: Create a folder specified by path
        path: String containing path to folder to create
        """
        if os.path.dirname(path) == '/':
            self.gd_client.CreateFolder(os.path.basename(path).encode(self.codec))
        else:
            parent_dir = self.get_filename(os.path.dirname(path), showfolders = 'true')
            self.gd_client.CreateFolder(os.path.basename(path).encode(self.codec), parent_dir)
            
    def move_file(self, pathfrom, pathto):
        """
        Purpose: Move a file from one folder to another
        pathfrom: String containing path to file to move
        pathto: String containing path to move to
        """
        folderfrom = os.path.dirname(pathfrom)
        folderto = os.path.dirname(pathto)
        namefrom = os.path.basename(pathfrom)

        if folderfrom != '/':
            ffe = self.get_filename(folderfrom, showfolders = 'true')
            feed = self.gd_client.GetDocumentListFeed(ffe.content.src)
            for entry in feed.entry:
                if unicode(entry.title.text, self.codec) == namefrom[:-4]:
                    entry_from = entry
            self.gd_client.MoveOutOfFolder(entry_from)
        
        entry_from = self.get_filename(pathfrom, showfolders = 'true')
            
        entry_to = self.get_filename(folderto, showfolders = 'true')
        type = entry_from.GetDocumentType()
        if type == 'folder':
            self.gd_client.MoveFolderIntoFolder(entry_from, entry_to)
        elif type == 'document':
            self.gd_client.MoveDocumentIntoFolder(entry_from, entry_to)
        elif type == 'spreadsheet':
            self.gd_client.MoveSpreadsheetIntoFolder(entry_from, entry_to)
        elif type == 'presentation':
            self.gd_client.MovePresentationIntoFolder(entry_from, entry_to)
        
        if os.path.basename(pathfrom) != os.path.basename(pathto):
            entry_from = self.rename_file(entry_from, os.path.basename(pathto))
        
        return 0
    
    def rename_file(self, entry, name_to):
        """
        Purpose: Renames an entry
        entry_from: GDataListEntry to change the name of
        name_to: String name to change to
        Returns: GDataListEntry of renamed file
        """
        entry.title.text = name_to
        return self.gd_client.Put(entry, entry.GetEditLink().href)        


def main():
    """
    Purpose: Used for Testing Only.
    Returns: 0 to indicate successful execution
    """
    return 0

if __name__ == '__main__':
    main()
