
sel_a_funA :: (a -> a) -> (a -> a)
sel_a_funA sel_a_funa_x0_1 = sel_a_funa_x0_1



test1 a_16_1 x_1 = (id :: a -> a) x_1

test4 :: (a -> a) -> a -> a
test4 a_30_1 x_9 = (sel_a_funA a_30_1 :: a -> a) x_9

test5 :: (a -> a) -> a -> a
test5 a_34_1 x_11 = (test1 a_34_1 :: a -> a) x_11

