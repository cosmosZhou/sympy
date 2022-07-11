from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Floor(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << sets.imply.any_el.real.apply(x)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.imply.et)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.le.ge.imply.ge.transit, ret=1)

    Eq << Eq[-1].this.expr.args[1:].apply(sets.lt.ge.imply.el.interval)

    Eq << Eq[-1].this.expr.args[1].apply(sets.el.imply.eq.floor)

    Eq << Eq[-1].this.expr.apply(algebra.ge.eq.imply.ge.transit)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-12-06
