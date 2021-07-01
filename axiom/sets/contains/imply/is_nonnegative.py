from util import *


@apply
def apply(given):
    x, R = given.of(Contains)
    [*_] = R.of(Interval[0, Infinity])
    assert x.is_complex
    return GreaterEqual(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(complex=True, given=True)
    Eq << apply(Contains(x, Interval(0, oo)))
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]
        

if __name__ == '__main__':
    run()

