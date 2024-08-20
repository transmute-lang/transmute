#!/usr/bin/env bash

ar rcs libobject.a object.o
clang main.c \
  -lobject -L. \
  -o lib

./lib 30

clang main.c assembly.s \
  -o asm

./asm 30