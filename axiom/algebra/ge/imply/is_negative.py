from util import *

import axiom


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    assert x < 0
    return Less(y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True, negative=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x >= y)
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    run()
