
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import Exists
from sympy.core.relational import LessThan
from sympy import Unequality
from axiom import sets, algebre


@apply(imply=True)
def apply(S):
    assert S.is_set
    
    x = S.element_symbol()
    y = S.element_symbol({x})
    return LessThan(abs(S), 1) | Exists[x:S, y:S](Unequality(x, y))




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)

    Eq << apply(S)
    
    Eq.strict_less_than, Eq.greater_than = Eq[-1].bisect(abs(S) >= 2).split()
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq.strict_less_than.limits)
    
    Eq << Eq[-1].apply(algebre.strict_less_than.imply.less_than)

    Eq << Eq.strict_less_than.split()[0]
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq.greater_than.limits)
    
    Eq << Eq[-1].apply(sets.greater_than.imply.exists_unequal)


if __name__ == '__main__':
    prove(__file__)

