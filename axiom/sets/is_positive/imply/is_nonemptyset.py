from sympy.core.relational import Unequal, Greater
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from axiom import algebra
# given: |A| > 0
# A != {}


@apply
def apply(given):
    assert isinstance(given, Greater)
    A_abs, zero = given.args
    assert A_abs.is_Abs and zero.is_extended_nonnegative
    A = A_abs.arg

    return Unequal(A, A.etype.emptySet)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    
    Eq << apply(abs(A) > 0)
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    prove()

