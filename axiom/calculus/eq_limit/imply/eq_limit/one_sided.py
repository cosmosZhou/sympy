from util import *


@apply
def apply(limited_f, dir=1):
    (fx, (x, x0, _dir)), A = limited_f.of(Equal[Limit])
    assert _dir == 0
    assert dir
    return Equal(Limit[x:x0:dir](fx), A)


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A), dir=1)

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.all.imply.infer)

    Eq << Eq[-1].this.find(~Less & Greater).apply(sets.abs_lt.given.el.interval)

    Eq << Eq[-1].this.find(Greater).apply(algebra.abs_gt.given.ou)

    Eq << Eq[-1].this.find(Expr < 0).apply(sets.lt_zero.given.is_negative, simplify=None)

    Eq << Eq[-1].this.find(Expr > 0).apply(sets.gt_zero.given.is_positive, simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.et.given.ou, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.given.cond, 1)

    Eq << Eq[-1].this.find(Element).apply(sets.el.given.el.add, x0)

    Eq << calculus.eq.given.any_all.limit_definition.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(algebra.all.given.infer)


if __name__ == '__main__':
    run()
# created on 2020-04-26
# updated on 2020-04-26
