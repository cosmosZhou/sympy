from sympy import *
from axiom.utility import prove, apply


@apply(simplify=False)
def apply(given, reverse=False):
    assert given.is_Contains
    x = given.generate_free_symbol(**given.lhs.type.dict)
    
    if reverse:
        return Exists[x:given.rhs](Equal(x, given.lhs))
    return Exists[x:given.rhs](Equal(given.lhs, x))


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

