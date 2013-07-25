
import SyntaxCheck (D (funD1, funD3))

test1 x = funD1 x
test2 x = funD3 x

test3 x = SyntaxCheck.funD1 x
test4 x = SyntaxCheck.funD3 x
