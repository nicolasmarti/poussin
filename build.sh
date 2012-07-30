#!/bin/sh

set -e

APPS=apps.otarget
TESTS=tests.otarget
FLAGS=""
OCAMLBUILD=ocamlbuild

ocb()
{
  $OCAMLBUILD $FLAGS $*
}

rule() {
  case $1 in
    clean)  ocb -clean;;
    all)    ocb $APPS; ocb $TESTS;;
    app)  ocb $APPS;;
    tests) ocb $TESTS;;
    gc)    clang -DWITHMAIN -o _build/gc ./lib/llvm/runtime/gc.c;;
    *)      echo "Unknown action $1";;
  esac;
}

if [ $# -eq 0 ]; then
  rule all
else
  while [ $# -gt 0 ]; do
    rule $1;
    shift
  done
fi

