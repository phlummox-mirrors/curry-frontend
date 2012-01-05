#!/bin/bash

subdir=".curry"
compilers="cymake cymake_pakcs"
modules="*.curry"
targets="flat xml acy uacy"

if [ $# -eq 1 ]; then
  targets=$1
fi

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
      $comp -e --$tgt $mdl
    done
  done
done

rm -rf $subdir

# show differences
echo "Differences"
echo "==========="
diff -brq $compilers

