from sympy.core.relational import Unequality, GreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
# given: |A| >= 1
# A != {}


@plausible
def apply(given):
    assert isinstance(given, GreaterThan)
    A_abs, positive = given.args
    assert A_abs.is_Abs and positive.is_positive
    A = A_abs.arg

    return Unequality(A, A.etype.emptySet)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    
    Eq << apply(abs(A) >= 1)
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].abs()
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

