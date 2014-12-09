#!/bin/sh

# This test runs several tests using "currytest". It checks for example
# the correctness of the type classes Prelude and the correctness of
# derived instances. 

if [ ! $1 ]; then
  echo Warning: using default Kics2 home
  echo Use \"test4.sh \<Kics2Home\>\" if you want to set a different home
  KICSHOME=../../..
else
  KICSHOME=$1
fi

# make kics home path absolute, because next we change the directory
# and the relative path would get invalid
KICSHOME=`readlink -f $KICSHOME`

cd typeclasses/kics2

./doTest $KICSHOME --gui



