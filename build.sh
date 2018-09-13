#!/bin/bash

eval `opam config env`
coq_makefile -f _CoqProject *.v > Makefile
make -j
