from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given, var=None):
    lhs, rhs = axiom.is_Unequal(given)
    if var is None:
        var = given.generate_free_symbol(**lhs.type.dict)
    return Equal(KroneckerDelta(lhs, var) * KroneckerDelta(rhs, var), 0)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(x, y), k)
    Eq << ~Eq[-1]
        
    Eq << Eq[-1].this.function.apply(algebra.is_nonzero.imply.et)
    
    Eq << algebra.exists_et.imply.exists.limits_delete.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    prove()
