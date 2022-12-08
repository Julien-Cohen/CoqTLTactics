#!/bin/sh
coq_makefile -f _CoqProject -o Makefile
make -j 4 
