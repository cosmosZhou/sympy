from util import *


@apply
def apply(given):
    n, a = given.of(NotContains[Interval[Infinity]])        
    return Less(n, a)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)

    Eq << apply(NotContains(x, Interval(a, oo)))
        
    Eq << ~Eq[0]
    
    Eq <<= Eq[-1] & Eq[1]

    
if __name__ == '__main__':
    run()

