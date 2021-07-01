from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr <= 0)
    return LessEqual(x, y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(GreaterEqual(0, a - b))
    
    Eq << Eq[0] + b
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    run()
