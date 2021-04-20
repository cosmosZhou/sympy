from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(S):
    assert S.is_set
    
    x = S.element_symbol()
    y = S.element_symbol({x})
    return LessEqual(abs(S), 1) | Exists[x:S, y:S](Unequal(x, y))


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)

    Eq << apply(S)
    
    Eq << Eq[-1].apply(algebra.cond.given.et.forall, cond=abs(S) >= 2)
    
    Eq.lt, Eq.ge = algebra.et.given.cond.apply(Eq[-1])
    
    Eq << algebra.imply.forall.limits_assert.apply(Eq.lt.limits)
    
    Eq << Eq[-1].this.function.apply(algebra.lt.imply.le.strengthen)
    
    Eq << algebra.forall_ou.given.forall.apply(Eq.lt, index=0)
    
    Eq << algebra.imply.forall.limits_assert.apply(Eq.ge.limits)
    
    Eq << Eq[-1].this.function.apply(sets.ge.imply.exists_ne)


if __name__ == '__main__':
    prove()

