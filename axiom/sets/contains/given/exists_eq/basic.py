from sympy import *
from axiom.utility import prove, apply


@apply
def apply(imply):
    assert imply.is_Contains
    x = imply.generate_free_symbol(**imply.lhs.type.dict)
    
    return Exists[x:imply.rhs](Equal(imply.lhs, x))


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(x, S))
    
    Eq << Eq[1].simplify()
    
if __name__ == '__main__':
    prove(__file__)

