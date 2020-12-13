
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import Exists
from sympy.core.relational import LessThan
from sympy import Unequality
from axiom import sets, algebre


@plausible
def apply(S):
    assert S.is_set
    
    x = S.element_symbol()
    y = S.element_symbol({x})
    return LessThan(abs(S), 1) | Exists[x:S, y:S](Unequality(x, y))


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(etype=dtype.real)

    Eq << apply(S)
    
    Eq.strict_less_than, Eq.greater_than = Eq[-1].bisect(abs(S) >= 2).split()
    
    Eq << sets.imply.forall.limits_assert.apply(Eq.strict_less_than.limits, simplify=False)
    
    Eq << Eq[-1].apply(algebre.strict_less_than.imply.less_than)

    Eq << Eq.strict_less_than.split()[0]
    
    Eq << sets.imply.forall.limits_assert.apply(Eq.greater_than.limits, simplify=False)
    
    Eq << Eq[-1].apply(sets.greater_than.imply.exists_inequality)


if __name__ == '__main__':
    prove(__file__)

