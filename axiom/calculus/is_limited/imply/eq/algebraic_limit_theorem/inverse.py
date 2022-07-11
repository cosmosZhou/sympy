from util import *


@apply
def apply(is_limited):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(is_limited, nonzero=True)

    return Equal(Limit[x:x0:dir](1 / fx), 1 / is_limited.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Reals - {0}))

    epsilon0 = Symbol('epsilon_0', real=True, positive=True)
    delta0 = Symbol('delta_0', real=True, positive=True)
    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], epsilon0, delta0, var='A')

    A = Eq[-1].expr.expr.find(Add[-~Symbol])
    Eq.is_limited = A.this.definition.reversed

    Eq.is_nonzero_real = Eq[0].subs(Eq.is_limited)

    Eq << sets.el.imply.ne_zero.apply(Eq.is_nonzero_real)

    Eq << algebra.ne_zero.eq.imply.eq.inverse.apply(Eq[-1], Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.is_limited)

    delta1 = Symbol(positive=True)
    Eq << calculus.eq.el.imply.any_all.lt.half.apply(Eq.is_limited, Eq.is_nonzero_real, delta=delta1)

    Eq.A_is_positive = sets.is_nonzero_real.imply.gt_zero.abs.apply(Eq.is_nonzero_real)

    Eq << algebra.cond.any_all.imply.any_all_et.apply(Eq.A_is_positive / 2, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(algebra.gt_zero.gt.imply.lt.inverse)

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq.A_is_positive)

    Eq << algebra.cond.any_all.imply.any_all_et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(algebra.gt_zero.lt.imply.lt.mul)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.lt.imply.lt.mul)

    Eq << Eq[-1].this.find(Mul[Abs]).apply(algebra.mul.to.abs)

    Eq << Eq[-1].this.find(Abs[~Mul]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.expr.expr.lhs.apply(algebra.abs.neg)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(sets.lt.given.el.interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(sets.lt.given.el.interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[1].simplify()

    epsilon, delta = Symbol(positive=True)
    Eq << algebra.cond.imply.ou.subs.apply(Eq[-1], epsilon0, abs(A) ** 2 / 2 * epsilon)

    Eq << algebra.gt_zero.imply.gt_zero.square.apply(Eq.A_is_positive) * epsilon / 2

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(delta0, delta1), delta)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-18
