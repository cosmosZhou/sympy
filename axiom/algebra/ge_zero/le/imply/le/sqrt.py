from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    _x, y = le.of(Expr <= Expr)
    assert x == _x

    return LessEqual(sqrt(x), sqrt(y))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, LessEqual(x, y))

    Eq << algebra.ge_zero.imply.sqrt_ge_zero.apply(Eq[0])

    t = Symbol(nonnegative=True)
    Eq << algebra.ge.imply.ou.split.apply(Eq[-1], t)

    Eq.ou = Eq[-1].subs(t, sqrt(y))

    Eq << algebra.le.ge.imply.ge.transit.apply(Eq[1], Eq[0])

    Eq << algebra.ge_zero.imply.sqrt_ge_zero.apply(Eq[-1])

    Eq << sets.ge.imply.el.interval.apply(Eq[-1])

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[-1], Eq.ou, invert=True)

    Eq << Eq[-1].this.args[1].apply(algebra.gt.imply.gt.square)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[1], Eq[-1], invert=True)

    Eq << algebra.et.imply.cond.apply(Eq[-1], 0)


if __name__ == '__main__':
    run()
# created on 2018-07-07
