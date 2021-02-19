from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    x = axiom.is_nonzero(given)
    assert x.is_nonnegative
    return StrictGreaterThan(x, 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True, nonnegative=True)

    Eq << apply(Unequal(a, 0))
    
    Eq << Contains(a, Interval(0, oo), plausible=True)
    
    Eq << sets.unequal.imply.notcontains.apply(Eq[0], simplify=False)
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-1].simplify()  


if __name__ == '__main__':
    prove(__file__)
