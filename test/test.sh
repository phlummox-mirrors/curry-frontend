
if [ ! $1 ]
then
  echo Usage: test.sh \<original_cymake\> [all]
  echo 
  echo Compares files compiled with the original cymake \(without typeclasses
  echo support\) with the files compiled with the new cymake \(with typeclasses
  echo support\)
  echo
  echo If the option all is not given, the test files are only compiled with the new
  echo cymake, not with the original, because it is enough, when the test files
  echo are compiled once with the original cymake. But if new test files are
  echo added, or this script is run the first time, this script must be called
  echo with the all option.
  echo
  echo The test files are in the directories lib and lib2\; in lib2, the test
  echo files are compiled with the original compiler, in lib, the test files
  echo are compiled with the new compiler
  exit
fi

cymake_orig=$1
cymake=../../dist/build/cymake/cymake

if [ "$2" = all ]
then
  rm -r -f lib2/.curry
 
  echo "=================="
  echo "building with orig"
  echo "=================="
  pushd lib2 ; $cymake_orig -e -f *.curry || exit 1; popd
  #pushd lib2/.curry/ && sed 's/$/ Nothing/' -s -i *.fint *.fcy && popd
fi

echo "=================="
echo "build with current"
echo "=================="

rm -r -f lib/.curry

pushd lib ; $cymake -e -f *.curry || exit 1; popd


./ComparePrograms.sh lib
