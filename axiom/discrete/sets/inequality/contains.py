from sympy.core.relational import Unequality, StrictGreaterThan, GreaterThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy.sets.contains import Contains
from sympy.concrete.expr_with_limits import Exists

# given: A != {}
# Exists[x] (x in A)


@plausible
def apply(given):
    assert given.is_Unequality
    A, B = given.args
    if B != S.EmptySet:
        assert A == S.EmptySet
        A = B
    x = A.element_symbol()
    return Exists(Contains(x, A), (x,), given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    Eq << apply(Unequality(A, S.EmptySet))
    
    Eq << (Eq[0].lhs.assertion() & Eq[0])
    
    Eq << Eq[-1].split()

if __name__ == '__main__':
    prove(__file__)

