#!/bin/bash

# This will start checkinstall with the basic information already filled in.
# If you're building your own package (e.g. RPM) then change -D to your
# package type and fill in appropriate details in checkinstall

checkinstall -D --install=no \
                --fstrans=yes \
                --pkgname=google-docs-fs \
                --pkgversion=1.0 \
                --pkgrelease=rc2 \
                --pkglicense=GPLv2 \
                --pkggroup=Office \
                --provides=google-docs-fs \
                --requires=python-gdata,python-fuse \
                --reset-uids=yes \
                --arch=all \
                ./setup.py build
