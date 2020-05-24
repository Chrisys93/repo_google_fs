README
Scott C. Walton
http://code.google.com/p/google-docs-fs

-------------------
SYSTEM REQUIREMENTS
-------------------

Python 2.5 or later
gdata-python-client-1.3.0 or later
python-fuse-0.2
Links to these can be found on the home page.

-----
LINUX
-----
To install in Linux run:

./setup.py install

as root.

--------
MAC OS X
--------
To install on Mac OSX do the following: 
1. Ensure you have the Mac-specific libraries above installed.
2. Download fuse-python.
3. Run the following commands

sudo cp /usr/local/lib/pkgconfig/fuse.pc /usr/local/lib/pkgconfig/fuse.bak
sudo sed -i 's#-I${includedir}/fuse -D_FILE_OFFSET_BITS=64#-I${includedir}/fuse -D__FreeBSD__=10 -D_FILE_OFFSET_BITS=64#g' /usr/local/lib/pkgconfig
sudo mv /usr/local/lib/pkgconfig/fuse.pc /usr/local/lib/pkgconfig/fuse.fix && sudo mv /usr/local/lib/pkgconfig/fuse.bak /usr/local/lib/pkgconfig/fuse.pc

4. Install fuse-python and gdata-python-client
5. Download and install the latest SVN revision of google-docs-fs

----------
KNOWN BUGS
----------

See the Issues page on the site listed above for the latest issues.

------
THANKS
------

Ben Samuel for his work in installing google-docs-fs on Mac OSX.
invernizzi.l for his work on providing a Ubuntu package.
miGlanz for writing the truncate() function, fixing Issue 6.
mr.xiaofan.li for finding and fixing Issue 23.
