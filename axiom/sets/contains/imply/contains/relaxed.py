from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


@apply
def apply(given, S):
    lhs, rhs = axiom.is_Contains(given)    
    return Contains(lhs, rhs | S)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    U = Symbol.U(etype=dtype.integer)
    S = Symbol.S(etype=dtype.integer)
    
    Eq << apply(Contains(e, U), S)
    
    Eq << sets.contains.given.ou.split.union.apply(Eq[1])
    
    Eq << algebra.cond.imply.ou.apply(Eq[0], cond=Contains(e, S))
    
if __name__ == '__main__':
    prove()

