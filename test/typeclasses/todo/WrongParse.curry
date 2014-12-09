
fun8 :: a -> a
fun8 = id

fun4 :: a -> a
fun4 = id

testI1 x = testI2 x

testI2 z =
  let x = fun8 y -- here a pattern declaration is created instead of a function declaration
      y = fun4 x -- dito
  in testI1 z

  