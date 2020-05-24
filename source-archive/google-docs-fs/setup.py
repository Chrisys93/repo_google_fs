#!/usr/bin/env python

import sys
from distutils.core import setup

required = []

setup(
    name='google-docs-fs',
    version='1.0rc2',
    description='Treat Google Docs as a local file system',
    author='Scott Walton',
    author_email='d38dm8nw81k1ng@gmail.com',
    license='GPLv2',
    url='http://code.google.com/p/google-docs-fs/',
    py_modules=['googledocsfs.gFile','googledocsfs.gNet'],
    scripts=['gmount','gumount','gmount.py'],
    install_requires=['python-fuse>=0.2','python-gdata>=2.0.0']
    )
