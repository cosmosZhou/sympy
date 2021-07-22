from util import *


@apply
def apply(x):
    return Greater(Floor(x), x - 1)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(real=True, given=True)
    Eq << apply(x)

    Eq << algebra.floor.to.maximize.apply(Eq[0].lhs)

    y = Symbol.y(Eq[1].lhs)
    Eq << y.this.definition

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << algebra.eq_maximize.imply.all_ge.apply(Eq[-1])

    Eq << Eq[0].subs(y.this.definition.reversed)

    Eq << ~Eq[-1]

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.expr.apply(algebra.le.ge.imply.le.transit)

    Eq << ~Eq[-1]

    Eq << algebra.any.given.any_et.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.gt.le.given.contains)

    n = Eq[-1].variable
    Eq << sets.imply.any_contains.integer.apply(x, n)


if __name__ == '__main__':
    run()

