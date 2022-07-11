from util import *


@apply(simplify=None)
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    return GreaterEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << sets.imply.any_el.real.left_open.apply(x)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.imply.et)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.le.ge.imply.ge.transit, ret=0)

    Eq << Eq[-1].this.expr.args[1:].apply(sets.gt.le.imply.el.interval)

    Eq << Eq[-1].this.expr.args[1].apply(sets.el.imply.eq.ceiling)

    Eq << Eq[-1].this.expr.apply(algebra.eq.ge.imply.ge.add)


if __name__ == '__main__':
    run()
# created on 2019-03-11
