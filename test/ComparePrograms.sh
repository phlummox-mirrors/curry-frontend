
# usage: cmpPrograms <lib dir>

if [ ! $1 ]
then
  echo Usage: ComparePrograms \<test files directory\>
  exit 1
fi

cmpPrograms=../dist/build/cmpPrograms/cmpPrograms

(cd $1/.curry && ls *.fcy) | xargs -i -n 1 $cmpPrograms $1/.curry/'{}' "$1"2/.curry/'{}' | tee errors.txt
(cd $1/.curry && ls *.fint) | xargs -i -n 1 $cmpPrograms $1/.curry/'{}' "$1"2/.curry/'{}' | tee -a errors.txt

(cat errors.txt | grep "Not equal") > errors2.txt

if [ -s errors2.txt ]
then

  echo "============================="
  echo "Errors: "
  echo "============================="

  cat errors2.txt
else
  echo "============================="
  echo "Test successfully passed"
fi

rm errors2.txt

exit 0
