from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, negate=False):
    x, M = axiom.is_LessEqual(given)
    x = axiom.is_Abs(x)
    if negate:
        x = -x
    return LessEqual(x, M)


@prove
def prove(Eq):
    M = Symbol.M(real=True)
    a = Symbol.a(real=True)
    
    Eq << apply(LessEqual(abs(a), M), negate=True)
    
    Eq << algebra.imply.le.abs.apply(a, negate=True)
    
    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq[0])

    
if __name__ == '__main__':
    prove()

