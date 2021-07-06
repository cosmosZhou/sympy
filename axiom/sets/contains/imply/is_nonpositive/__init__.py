from util import *


@apply
def apply(given):
    x, R = given.of(Contains)
    [*_] = R.of(Interval[-oo, 0])
    assert x.is_complex
    return LessEqual(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(complex=True, given=True)
    Eq << apply(Contains(x, Interval(-oo, 0)))
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]
    
        

if __name__ == '__main__':
    run()

from . import abs
