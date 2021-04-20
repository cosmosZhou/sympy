from axiom.utility import prove, apply
from sympy import *
from axiom import sets
import axiom


# given e not in S
@apply
def apply(given):
    e, S = axiom.is_NotContains(given)
    S = axiom.is_Intersection(S)
    return Or(*(NotContains(e, s) for s in S))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(NotContains(e, A & B))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].simplify()
    
    Eq << ~Eq[-1]

if __name__ == '__main__':
    prove()

