
cymake=../dist/build/cymake/cymake

rm -f output_test2_stderr.txt
rm -f output_test2_stdout.txt
rm -f tmp.txt

echo ================

# prepare needed interfaces

$cymake -f -i typeclasses typeclasses/Float.curry typeclasses/Prelude.curry > /dev/null
$cymake -f -i typeclasses/modules typeclasses/modules/Prelude.curry > /dev/null

# do the check # 1

for file in DictTrans1 DictTrans2 DictTrans3 DictTrans4 \
  DictTrans5 DictTrans6 DictTrans7 DictTrans8 DictTrans9 \
  DictTrans10 DictTrans11 DictTrans12 \
  Annot1 Annot2 Annot3 Annot4 Annot5 Annot6 Annot7\
  BugDicts BugDictTrans8 Annot_bug Annot_bug2 Annot_bug3 \
  PropagTest1 PropagTest2 PropagTest3 \
  BugAmbig2 \
  TypeSigsTrans BugTypeSigsTrans BugTypeSigsTrans2 \
  ClassEnv TCC GenElems TCC_Bug \
  Arb NullaryClassMethods \
  TypedExpressions2 DictionaryTypes \
  TestDictType \
  DefaultMethods1 DefaultMethods2 \
  BugClassMethodsVsPredefinedFuncs \
  BugTySigs \
  Example Example2 Example3 \
  DictOrderBug DictOrderBug2 DictOrderBug3 DictOrderBug4 DictOrderBug5 DictOrderBug6 DictOrderBug7 \
  TestMixedDeclGroups TypeSigPattern \
  ImplicBug ExtendedExample \
  QualifiedClassMethods Warnings ExpandClassTySigsTypes ExpandClassTySigs TypeSigProblem ContextRed \
  SelSuperclasses2 SelSuperclasses TestInstances2 TestInstances InstanceConstraints2 \
  TestVarious \
  DataConstructorsBug1 DataConstructorsBug2
do
  echo $file >> tmp.txt
  $cymake -f -i typeclasses typeclasses/$file.curry 2>> output_test2_stderr.txt 1>> output_test2_stdout.txt || echo Error in $file.curry
done

# Those files contain type classes with other type vars in methods than
# the type variable of the class and can thus not be checked:

# DictTrans5_orig DictTrans6_orig Annot1_orig
# Annot7_orig TypeSigsTrans_orig BugTypeSigsTrans_orig
# TypedExpressions2_orig


# do the check # 2 (modules system related)

for file in TestClassExports TestClassExports2 TestClassExportsImports \
  TestClassExportsNoExportSpec \
  InstancesExports InstancesExportsImports InstancesExportBug InstancesExportBugImports
do
  echo $file >> tmp.txt
  $cymake -f -i typeclasses/modules typeclasses/modules/$file.curry 2>> output_test2_stderr.txt 1>> output_test2_stdout.txt || echo Error in $file.curry
done

echo `cat tmp.txt | wc -l` files checked
rm tmp.txt


