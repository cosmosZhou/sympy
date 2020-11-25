from sympy.core.relational import GreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.concrete.expr_with_limits import Exists
from sympy.sets.contains import Contains
from axiom import algebre, sets
# given: |A| >= 1
# A != {}


@plausible
def apply(given):
    assert isinstance(given, GreaterThan)
    S_abs, positive = given.args
    assert S_abs.is_Abs and positive.is_extended_positive
    S = S_abs.arg

    x = S.element_symbol()

    return Exists[x](Contains(x, S), given=given)


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(etype=dtype.integer, given=True)
    
    Eq << apply(abs(S) >= 1)
    
    Eq << algebre.greater_than.imply.strict_greater_than.apply(Eq[0], 0)
    
    Eq << sets.is_positive.imply.exists_contains.apply(Eq[-1], simplify=False)
    

if __name__ == '__main__':
    prove(__file__)

