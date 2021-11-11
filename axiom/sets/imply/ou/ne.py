from util import *


@apply
def apply(S):
    assert S.is_set

    x = S.element_symbol()
    y = S.element_symbol({x})
    return LessEqual(Card(S), 1) | Any[x:S, y:S](Unequal(x, y))


@prove
def prove(Eq):
    from axiom import algebra, sets

    S = Symbol(etype=dtype.real)
    Eq << apply(S)

    Eq << Eq[-1].apply(algebra.cond.given.et.all, cond=Card(S) >= 2)

    Eq.lt, Eq.ge = algebra.et.given.et.apply(Eq[-1])

    Eq << algebra.imply.all.limits_assert.apply(Eq.lt.limits)

    Eq << Eq[-1].this.expr.apply(algebra.lt.imply.le.strengthen)

    Eq << algebra.all_ou.given.all.apply(Eq.lt)

    Eq << algebra.imply.all.limits_assert.apply(Eq.ge.limits)

    Eq << Eq[-1].this.expr.apply(sets.ge.imply.any_ne)


if __name__ == '__main__':
    run()

# created on 2020-07-16
# updated on 2020-07-16
