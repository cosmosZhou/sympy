from axiom.utility import prove, apply
from sympy import *
from axiom import sets
import axiom


# given e not in S
@apply
def apply(given, simplify=True):
    e, S = axiom.is_NotContains(given)
    U, A = axiom.is_Complement(S)
    contains = Contains(e, A)
    notcontains = NotContains(e, U)
    if simplify:
        contains = contains.simplify()
        notcontains = notcontains.simplify()
        
    return Or(notcontains, contains)


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    U = Symbol.U(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(NotContains(e, Complement(U, A)))
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].simplify()
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove()

