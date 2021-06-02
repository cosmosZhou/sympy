from util import *

@apply
def apply(given):
    n, b = given.of(NotContains[Interval[NegativeInfinity]])
    return Greater(n, b)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)

    Eq << apply(NotContains(x, Interval(-oo, a)))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq <<= Eq[0] & Eq[-1]

if __name__ == '__main__':
    run()

