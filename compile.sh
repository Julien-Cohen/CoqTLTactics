#!/bin/sh
coq_makefile -f _CoqProject -o Makefile
make -k -j 4 
