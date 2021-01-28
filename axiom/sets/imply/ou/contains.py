from sympy.core.relational import Equality, Unequal
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import Exists
from sympy.sets.contains import Contains

@apply(imply=True)
def apply(S):
    assert S.is_set
    
    e = S.element_symbol()
    return Exists(Contains(e, S), (e,)) | Equality(S, e.emptySet)




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)

    Eq << apply(S)
    
    Eq << Eq[-1].bisect(Unequal(S, S.etype.emptySet))
    
    Eq << Eq[-1].this.function.simplify()

if __name__ == '__main__':
    prove(__file__)

