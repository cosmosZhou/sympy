from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(limited_f, nonzero=True)
    gx, (_x, _x0, _dir) = of_limited(limited_g, real=True)
    assert dir == _dir

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0:dir](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    dir = S.One
    Eq << apply(Element(Limit[x:x0:dir](f(x)), Reals - {0}), Element(Limit[x:x0:dir](g(x)), Reals))

    ε = Symbol(real=True, positive=True)
    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq.limit_A_definition = calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    A = -Eq.limit_A_definition.expr.expr.lhs.arg.args[0]
    Eq << Eq[0].subs(A.this.definition.reversed)

    Eq.abs_gt_zero = sets.is_nonzero_real.imply.gt_zero.abs.apply(Eq[-1])

    Eq.abs_is_positive = sets.is_nonzero_real.imply.is_positive.abs.apply(Eq[-1], simplify=None)

    Eq << sets.is_nonzero_real.imply.is_nonzero_real.div.apply(Eq[-1])

    Eq << sets.is_nonzero_real.imply.is_positive.abs.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(algebra.abs.to.reciprocal, simplify=None)

    Eq.is_positive_real = sets.el.imply.el.mul.interval.apply(Eq[-1], ε / 2, simplify=None)

    ε_1 = Symbol(real=True, positive=True)
    δ_1 = Symbol(real=True, positive=True)
    Eq.limit_B_definition = calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[1], ε_1, δ_1, var='B')

    B = -Eq.limit_B_definition.expr.expr.lhs.arg.args[0]
    Eq << algebra.imply.le.abs.add.mul.apply(f(x), g(x), A, B)

    δ_2 = Symbol(real=True, positive=True)
    Eq << calculus.is_limited.imply.any_all.le.boundedness.apply(Eq[1], delta=δ_2, var='B')

    B = Eq[-1].expr.expr.rhs
    Eq.le = Eq[-1].this.expr.expr.apply(algebra.le.lt.imply.le.subs, Eq[-2])

    assert B > 0
    Eq << Eq.limit_A_definition.subs(ε_0, ε / B / 2)

    Eq.lt_fx = Eq[-1].this.expr.expr * B

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq.abs_gt_zero, ε / 2, simplify=None)

    Eq << Eq.limit_B_definition.subs(ε_1, Eq[-1].lhs)

    Eq << algebra.cond.ou.imply.cond.apply(Eq.is_positive_real, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(sets.lt.is_positive.imply.lt.mul, Eq.abs_is_positive)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[-1], Eq.lt_fx)

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.lt.imply.lt.add)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq.le, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.le.imply.lt.transit)

    Eq << Eq[-1].this.expr.apply(algebra.all.imply.infer)

    Eq << Eq[-1].this.find(Element).apply(sets.el.given.el.sub, x0)

    Eq << Eq[-1].this.find(Add[Min]).apply(algebra.add.to.min)

    delta = Symbol(real=True, positive=True)
    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(δ_0, δ_1, δ_2), delta)

    Eq << Eq[-1].this.find(Element).apply(sets.el.given.el.add, x0)

    Eq << Eq[-1].this.expr.apply(algebra.infer.imply.all)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].definition





if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

# created on 2020-04-16
# updated on 2021-10-02