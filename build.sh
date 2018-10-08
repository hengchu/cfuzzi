#!/bin/bash

eval `opam config env`
coq_makefile -f _CoqProject -o Makefile
make -j
