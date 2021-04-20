from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, negate=False):
    x, M = axiom.is_Less(given)
    x = axiom.is_Abs(x)
    if negate:
        x = -x
    return Less(x, M)


@prove
def prove(Eq):
    M = Symbol.M(real=True)
    a = Symbol.a(real=True)
    
    Eq << apply(Less(abs(a), M), negate=True)

    Eq << algebra.imply.le.abs.apply(a, negate=True)
    
    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[0])

    
if __name__ == '__main__':
    prove()

