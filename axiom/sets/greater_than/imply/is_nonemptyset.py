from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
# given: |A| >= 1
# A != {}


@apply
def apply(given):
    assert isinstance(given, GreaterThan)
    S_abs, positive = given.args
    assert S_abs.is_Abs and positive.is_extended_positive
    S = S_abs.arg

    x = S.element_symbol()

    return Unequal(S, S.etype.emptySet)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer, given=True)
    
    Eq << apply(abs(S) >= 1)
    
    Eq << algebre.greater_than.imply.strict_greater_than.transit.apply(Eq[0], 0)
    
    Eq << sets.is_positive.imply.is_nonemptyset.apply(Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

