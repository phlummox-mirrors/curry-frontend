
cymake=../dist/build/cymake/cymake
cymake_orig=../dist/build/cymake/cymake_orig

echo ================

for file in Annot7 DictTrans2 DictTrans3 Annot6 DictTrans8 BugDicts BugDictTrans8 Annot_bug 
do
  $cymake -f typeclasses/$file.curry 2> /dev/null 1> /dev/null || echo Error in $file.curry
done
