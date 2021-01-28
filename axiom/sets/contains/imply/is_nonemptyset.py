from sympy.core.relational import Unequality
from axiom.utility import prove, apply
from sympy.sets.contains import NotContains, Contains
from sympy import Symbol
import axiom
from sympy.core.symbol import dtype
# given: x != y
# x not in {y}


@apply(imply=True)
def apply(given):
    x, S = axiom.is_Contains(given)
    return Unequality(S, x.emptySet)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    S = Symbol.S(etype=dtype.complex * n, given=True)
    Eq << apply(Contains(x, S))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[0].subs(Eq[-1])
        

if __name__ == '__main__':
    prove(__file__)

