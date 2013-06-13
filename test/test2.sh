
cymake=../dist/build/cymake/cymake
cymake_orig=../dist/build/cymake/cymake_orig

echo ================
  
for file in DictTrans1 DictTrans2 DictTrans3 DictTrans4 \
  DictTrans5 DictTrans6 DictTrans7 DictTrans8 DictTrans9 \
  DictTrans10 \
  Annot1 Annot2 Annot3 Annot4 Annot5 Annot6 Annot7\
  BugDicts BugDictTrans8 Annot_bug Annot_bug2 Annot_bug3 \
  PropagTest1 PropagTest2 PropagTest3 \
  BugAmbig2 \
  TypeSigsTrans
do
  #echo $file
  $cymake -f typeclasses/$file.curry 2> /dev/null 1> /dev/null || echo Error in $file.curry
done
