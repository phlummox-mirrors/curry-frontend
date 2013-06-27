
cymake=../../dist/build/cymake/cymake
cymake_orig=../../dist/build/cymake/cymake_orig


if [ "$1" = all ]
then
  echo "=================="
  echo "building with orig"
  echo "=================="
  pushd lib2 && $cymake_orig -e -f *.curry && popd
  #pushd lib2/.curry/ && sed 's/$/ Nothing/' -s -i *.fint *.fcy && popd
fi

echo "=================="
echo "build with current"
echo "=================="

pushd lib && $cymake -e -f *.curry && popd


./ComparePrograms.sh lib
