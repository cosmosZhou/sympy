from sympy.core.relational import Unequality, StrictGreaterThan
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from axiom import algebre
# given: |A| > 0
# A != {}


@apply(imply=True)
def apply(given):
    assert isinstance(given, StrictGreaterThan)
    A_abs, zero = given.args
    assert A_abs.is_Abs and zero.is_extended_nonnegative
    A = A_abs.arg

    return Unequality(A, A.etype.emptySet)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    
    Eq << apply(abs(A) > 0)
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

