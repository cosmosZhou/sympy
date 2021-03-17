from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply
def apply(S):
    assert S.is_set
    
    x = S.element_symbol()
    y = S.element_symbol({x})
    return LessThan(abs(S), 1) | Exists[x:S, y:S](Unequality(x, y))


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)

    Eq << apply(S)
    
    Eq << Eq[-1].bisect(abs(S) >= 2)
    
    Eq.lt, Eq.ge = algebre.et.given.cond.apply(Eq[-1])
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq.lt.limits)
    
    Eq << Eq[-1].apply(algebre.lt.imply.le.strengthen)
    
    Eq << algebre.forall_ou.given.forall.apply(Eq.lt, index=0)
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq.ge.limits)
    
    Eq << Eq[-1].apply(sets.ge.imply.exists_ne)


if __name__ == '__main__':
    prove(__file__)

