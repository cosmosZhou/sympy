from util import *


@apply(simplify=False)
def apply(given):
    lhs, rhs = given.of(Equal)    
    return Equal(rhs, lhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(Equal(x, y))
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    run()

