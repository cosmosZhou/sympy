from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.sets.contains import NotContains
from axiom import sets
import axiom
from sympy import ForAll


# given A & B = {} => A - B = A
@plausible
def apply(given, wrt=None):
    AB = axiom.is_emptyset(given)

    A, B = axiom.is_Intersection(AB)
    if wrt is None:
        wrt = given.generate_free_symbol(**A.etype.dict)
        
    return ForAll[wrt: A](NotContains(wrt, B))


from axiom.utility import check


@check
def prove(Eq):
    B = Symbol.B(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(Equality(A & B, A.emptySet))
    
    Eq << ~Eq[1]
    
    Eq << sets.exists.imply.exists_et.single_variable.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
    


if __name__ == '__main__':
    prove(__file__)

