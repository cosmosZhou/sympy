from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    assert given.is_Contains
    e, domain = given.args
    args = axiom.is_Intersection(domain)
    
    return And(*(Contains(e, s) for s in args))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A & B))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove()

