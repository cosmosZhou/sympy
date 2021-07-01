from util import *


@apply(simplify=False)
def apply(given, reverse=False, var=None):
    lhs, rhs = given.of(Contains)
    if var is None:
        x = given.generate_var(**rhs.etype.dict)
    else:
        if isinstance(var, str):
            x = given.generate_var(var=var, **rhs.etype.dict)
        else:
            x = var
    
    if reverse:
        return Any[x:rhs](Equal(x, lhs))
    return Any[x:rhs](Equal(lhs, x))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(x, S))
    
    Eq << Eq[1].simplify()

    
if __name__ == '__main__':
    run()

from . import split
