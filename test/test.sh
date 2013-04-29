
cymake=../../dist/build/cymake/cymake
cymake_orig=../../dist/build/cymake/cymake_orig


pushd lib && $cymake -e -f *.curry && popd

if [ "$1" = all ]
then
  echo "building with orig"
  pushd lib2 && $cymake_orig -e -f *.curry && popd
  pushd lib2/.curry/ && sed 's/$/ Nothing/' -s -i *.fint *.fcy && popd
fi

./ComparePrograms.sh lib
