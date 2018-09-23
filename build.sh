#!/bin/bash

eval `opam config env`
coq_makefile -f _CoqProject > Makefile
make -j
