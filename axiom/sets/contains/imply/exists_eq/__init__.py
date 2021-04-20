from sympy import *
from axiom.utility import prove, apply


@apply(simplify=False)
def apply(given, reverse=False, var=None):
    assert given.is_Contains
    if var is None:
        x = given.generate_free_symbol(**given.rhs.etype.dict)
    else:
        if isinstance(var, str):
            x = given.generate_free_symbol(free_symbol=var, **given.rhs.etype.dict)
        else:
            x = var
    
    if reverse:
        return Exists[x:given.rhs](Equal(x, given.lhs))
    return Exists[x:given.rhs](Equal(given.lhs, x))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(x, S))
    
    Eq << Eq[1].simplify()

    
if __name__ == '__main__':
    prove()

from . import split
