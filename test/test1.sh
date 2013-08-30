
if [ ! $1 ]
then
  echo Usage: test1.sh \<original_cymake\> [all]
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
  echo The test files are in the directories typeclasses/comparetest_orig and
  echo typeclasses/comparetest_new\; in comparetest_orig, the test
  echo files are compiled with the original compiler, in comparetest_new,
  echo the test files are compiled with the new compiler. 
  exit 1
fi

cymake_orig=`readlink -f $1`
cymake=`readlink -f ../dist/build/cymake/cymake`

if [ "$2" = all ]
then
  rm -r -f typeclasses/comparetest_orig/.curry
 
  echo "=================="
  echo "building with orig"
  echo "=================="
  pushd typeclasses/comparetest_orig ; $cymake_orig -e -f *.curry || exit 1; popd
  #pushd typeclasses/comparetest_orig/.curry/ && sed 's/$/ Nothing/' -s -i *.fint *.fcy && popd
fi

echo "=================="
echo "build with current"
echo "=================="

rm -r -f typeclasses/comparetest_new/.curry

pushd typeclasses/comparetest_new ; $cymake -e -f *.curry || exit 1; popd


./ComparePrograms.sh typeclasses/comparetest_orig typeclasses/comparetest_new

exit $?
