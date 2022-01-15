from util import *


@apply
def apply(all_is_positive):
    (fx, (x, d)), (x_, domain) = all_is_positive.of(All[Derivative > 0])
    assert x == x_

    assert domain.left_open and domain.right_open

    return All[x:domain](Element(Derivative(fx, (x, d)), Interval(0, oo, left_open=True)))


@prove
def prove(Eq):
    from axiom import sets, algebra, calculus

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(extended_real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[0].this.expr.apply(sets.gt_zero.imply.is_extended_positive)

    Eq << ~Eq[1]

    Eq << algebra.all.any.imply.any_et.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.lhs.apply(calculus.derivative.to.limit)

    Eq << Eq[-1].this.expr.apply(calculus.eq_limit.imply.et.eq_limit)

    Eq << Eq[-1].this.expr.args[0].apply(calculus.limit_is_infinite.imply.lt.limit)

    Eq << Eq[-1].this.expr.args[1].apply(calculus.limit_is_infinite.imply.gt.limit)




if __name__ == '__main__':
    run()
# created on 2020-04-28
