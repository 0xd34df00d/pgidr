#! /bin/sh

set -e

gcc -O2 -o libpgidr-cbits.so cbits/cbits.c -shared 
