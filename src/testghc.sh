#!/bin/sh

[ -f "Makefile_support" ] && rm -f Makefile_support

GHCVS=`ghc -V`
GHCMajorV=`expr "$GHCVS" : ".*version \([0-9]*\).*"`
GHCMinorV=`expr "$GHCVS" : ".*version [0-9]*\.\([0-9]*\).*"`


if test $GHCMajorV -lt 6 ; then
  echo "# Just for ghc < 6" > Makefile_support 
  echo "HC_OPTS	+= -syslib lang" >> Makefile_support
elif  test $GHCMajorV -eq 6 -a $GHCMinorV -lt 6 ; then 
  echo "# Just for ghc < 6.6" > Makefile_support 
  echo "HC_OPTS	+= -syslib lang" >> Makefile_support
fi
