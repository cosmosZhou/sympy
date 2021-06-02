from util import *

import axiom


@apply
def apply(given):
    x, y = given.of(LessEqual)
    assert x > 0
    return Greater(y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True, positive=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x <= y)
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    run()
