from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebra
import axiom


# given e not in S
@apply
def apply(imply):
    e, S = axiom.is_NotContains(imply)
    U, A = axiom.is_Complement(S)
    return Or(NotContains(e, U), Contains(e, A).simplify())


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    U = Symbol.U(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(NotContains(e, Complement(U, A)))
    
    Eq << ~Eq[0]
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1])


if __name__ == '__main__':
    prove()

