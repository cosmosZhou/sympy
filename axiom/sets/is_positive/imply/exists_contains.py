
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy.sets.contains import Contains
from sympy import Exists
from sympy import Symbol
from axiom import sets
# given: A >= 1
# Exists[x] (x in A)


@apply(imply=True)
def apply(given):
    assert given.is_StrictGreaterThan
    abs_S, size = given.args
    assert size.is_extended_nonnegative
    assert abs_S.is_Abs
    S = abs_S.arg
    x = S.element_symbol()
    return Exists[x](Contains(x, S))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    Eq << apply(abs(A) > 0)
    
    Eq << sets.is_positive.imply.is_nonemptyset.apply(Eq[0])
    
    Eq << sets.is_nonemptyset.imply.exists_contains.emptyset.apply(Eq[-1], simplify=False)
    

if __name__ == '__main__':
    prove(__file__)

