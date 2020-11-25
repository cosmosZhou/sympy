from sympy.core.relational import Unequality, StrictGreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
# given: |A| > 0
# A != {}


@plausible
def apply(given):
    assert isinstance(given, StrictGreaterThan)
    A_abs, zero = given.args
    assert A_abs.is_Abs and zero.is_extended_nonnegative
    A = A_abs.arg

    return Unequality(A, A.etype.emptySet, given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    
    Eq << apply(abs(A) > 0)
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].abs()
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

