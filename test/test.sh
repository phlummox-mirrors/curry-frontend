
cymake=../../dist/build/cymake/cymake
cymake_orig=../../dist/build/cymake/cymake_orig


if [ "$1" = all ]
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
