from util import *


@apply
def apply(le, contains0, contains1, all_is_positive):
    (fx, (x, d)), (x_, domain) = all_is_positive.of(All[Derivative > 0])
    assert x == x_

    assert domain.left_open and domain.right_open
    x0, domain_ = contains0.of(Element)
    assert domain_ == domain

    x1, domain_ = contains1.of(Element)
    assert domain_ == domain

    _x0, _x1 = le.of(LessEqual)
    assert x0 == _x0
    assert x1 == _x1

    d -= 1
    if d:
        fx = Derivative(fx, (x, d))

    f = lambda x: fx._subs(x_, x)
    return f(x0) <= f(x1)


@prove
def prove(Eq):
    from axiom import sets, calculus, algebra

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(x0 <= x1, Element(x0, domain), Element(x1, domain), All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[3].this.expr.apply(sets.gt.imply.is_extended_real)
    Eq.subset = sets.el.el.imply.subset.interval.apply(Eq[1], Eq[2])
    Eq << sets.subset.all.imply.all.apply(Eq.subset, Eq[-1])
    Eq << calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])
    Eq.any = calculus.le.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.close.apply(Eq[0], Eq[-1], Eq[-2])
    Eq << sets.subset.all.imply.all.apply(Eq.subset, Eq[3])
    Eq << sets.all.imply.all_et.apply(Eq[-1], simplify=None)
    Eq << Eq[-1].this.find(Unequal).apply(sets.interval_ne_empty.imply.ge_zero, simplify=None)
    Eq << Eq[-1].this.expr.apply(algebra.ge_zero.gt_zero.imply.ge_zero)
    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq.any)
    Eq << Eq[-1].this.expr.apply(algebra.ge.eq.imply.ge.transit)
    Eq << algebra.et.imply.et.apply(Eq[-1])
    Eq << algebra.ge_zero.imply.le.apply(Eq[-2])
    
    


if __name__ == '__main__':
    run()
# created on 2020-05-10
# updated on 2022-01-19
