from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << sets.imply.any_el.real.left_open.apply(x)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.imply.et)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.gt.le.imply.lt.transit, ret=0)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.lt.imply.le.strengthen)

    Eq << Eq[-1].this.expr.args[0] + 1

    Eq << Eq[-1].this.expr.args[1:].apply(sets.gt.le.imply.el.interval)

    Eq << Eq[-1].this.expr.args[1].apply(sets.el.imply.eq.ceiling)

    Eq << Eq[-1].this.expr.apply(algebra.eq.le.imply.le.add)


if __name__ == '__main__':
    run()
# created on 2018-10-30
