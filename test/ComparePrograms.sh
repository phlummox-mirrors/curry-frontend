
# usage: cmpPrograms <lib dir>

if [ ! $1 -o ! $2 ]
then
  echo Usage: ComparePrograms \<test files directory 1 \(orig\)\>
  echo "                      " \<test files directory 2 \(new\)\>
  exit 1
fi

cmpPrograms=../dist/build/cmpPrograms/cmpPrograms

(cd $1/.curry && ls *.fcy) | xargs -i -n 1 $cmpPrograms $1/.curry/'{}' $2/.curry/'{}' | tee errors.txt
(cd $1/.curry && ls *.fint) | xargs -i -n 1 $cmpPrograms $1/.curry/'{}' $2/.curry/'{}' | tee -a errors.txt

(cat errors.txt | grep "Not equal") > errors2.txt

if [ -s errors2.txt ]
then

  echo "============================="
  echo "Errors: "
  echo "============================="

  cat errors2.txt

  exitCode=1
else
  echo "============================="
  echo "Test successfully passed"

  exitCode=0
fi

rm errors2.txt

exit $exitCode
