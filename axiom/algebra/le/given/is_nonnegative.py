from util import *

import axiom


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return GreaterEqual(y - x, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x <= y)
    
    Eq << Eq[1] - y
    
    Eq << -Eq[-1]
    

if __name__ == '__main__':
    run()
