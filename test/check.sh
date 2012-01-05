#!/bin/bash

subdir=".curry"
compilers="cymake cymake_pakcs"
modules="*.curry"
targets="flat xml acy uacy"
importdir="."

function usage()
{
  echo "Usage: check.sh [OPTIONS] modules"
  echo "Compare old and new frontend against each other"
  echo ""
  echo "  -i DIR  , --import-dir DIR   Search for libraries in DIR"
  echo "  -i EXTS , --targets EXTS     Create the target types EXTS (some of flat, xml, acy, uacy)"
  echo "  -h      , --help             Show this help and exit"
}

while [ "$1" != "" ]; do
  case $1 in
    -i | --import-dir  )    shift
                            importdir=$1
                            ;;
    -t | --targets     )    shift
                            targets=$1
                            ;;
    -h | --help )           usage
                            exit
                            ;;
    * )                     modules=$*
                            break
  esac
  shift
done

for comp in $compilers; do
  echo -e "$comp\n============"

  # clean up before using the compiler
  rm -f  $comp/*
  rm -rf $subdir
  if [ ! -d $comp ]; then
    mkdir $comp
  fi
  ln -s  $comp/  $subdir

  # compile targets
  for mdl in $modules; do
    for tgt in $targets; do
      $comp -e -i $importdir --$tgt $mdl
    done
  done
done

rm -rf $subdir

# show differences
echo "Differences"
echo "==========="
diff -brq $compilers

