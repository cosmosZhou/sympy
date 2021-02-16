from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebre


@apply(imply=True)
def apply(given, S):
    lhs, rhs = axiom.is_Contains(given)    
    return Contains(lhs, rhs | S)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    U = Symbol.U(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    S = Symbol.S(etype=dtype.integer)
    
    Eq << apply(Contains(e, U), S)
    
    Eq << sets.contains.given.ou.apply(Eq[1])
    
    Eq << algebre.condition.imply.ou.apply(Eq[0], Contains(e, S))
    
if __name__ == '__main__':
    prove(__file__)

