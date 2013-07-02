
cymake=../dist/build/cymake/cymake
cymake_orig=../dist/build/cymake/cymake_orig

echo ================
  
for file in DictTrans1 DictTrans2 DictTrans3 DictTrans4 \
  DictTrans5 DictTrans6 DictTrans7 DictTrans8 DictTrans9 \
  DictTrans10 DictTrans12 \
  Annot1 Annot2 Annot3 Annot4 Annot5 Annot6 Annot7\
  BugDicts BugDictTrans8 Annot_bug Annot_bug2 Annot_bug3 \
  PropagTest1 PropagTest2 PropagTest3 \
  BugAmbig2 \
  TypeSigsTrans BugTypeSigsTrans BugTypeSigsTrans2 \
  ClassEnv TCC GenElems \
  Arb NullaryClassMethods \
  TypedExpressions2 DictionaryTypes
do
  #echo $file
  $cymake -f typeclasses/$file.curry 2>> output_test2_stderr.txt 1>> output_test2_stdout.txt || echo Error in $file.curry
done


# Those files contain type classes with other type vars in methods than
# the type variable of the class and can thus not be checked:

# DictTrans5_orig DictTrans6_orig Annot1_orig
# Annot7_orig TypeSigsTrans_orig BugTypeSigsTrans_orig
# TypedExpressions2_orig


