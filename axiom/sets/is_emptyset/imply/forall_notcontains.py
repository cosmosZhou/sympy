from axiom.utility import prove, apply
from sympy import *
from axiom import sets
import axiom


# given A & B = {} => A - B = A
@apply
def apply(given, wrt=None):
    AB = axiom.is_emptyset(given)

    A, B = axiom.is_Intersection(AB)
    if wrt is None:
        wrt = given.generate_free_symbol(**A.etype.dict)
        
    return ForAll[wrt:A](NotContains(wrt, B))


@prove
def prove(Eq):
    B = Symbol.B(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(Equal(A & B, A.emptySet))
    
    Eq << ~Eq[1]
    
    Eq << sets.exists.imply.exists_et.single_variable.apply(Eq[-1])
    
    Eq << sets.exists_contains.imply.is_nonemptyset.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove()

