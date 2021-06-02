from util import *


@apply
def apply(given):
    x, R = given.of(Contains)
    start, stop = R.of(Interval)
    if R.left_open:        
        assert start >= 0
    else:
        assert start > 0
    assert stop == oo
    assert x.is_complex
    
    return Greater(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(complex=True, given=True)
    Eq << apply(Contains(x, Interval(0, oo, left_open=True)))
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]
    
        

if __name__ == '__main__':
    run()

from . import abs
