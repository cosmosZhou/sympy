from sympy.core.relational import Unequality, StrictGreaterThan, GreaterThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.abc import *
from sympy.sets.sets import EmptySet

# given: |A| > 0
# A != {}


@plausible
def apply(given):
    assert isinstance(given, StrictGreaterThan)
    A_abs, zero = given.args
    assert A_abs.is_Abs and zero == 0
    A = A_abs.arg

    return Unequality(A, EmptySet(), given=given)


from sympy.utility import check


@check
def prove(Eq):
    A in dtype.integer.set
    
    Eq << apply(abs(A) > 0)
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].abs()
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

