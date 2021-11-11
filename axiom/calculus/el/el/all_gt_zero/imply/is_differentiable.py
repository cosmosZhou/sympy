from util import *


@apply
def apply(contains0, contains1, all_is_positive):
    x0, _domain = contains0.of(Element)
    x1, __domain = contains1.of(Element)
    (fx, (x, d)), (x_, domain) = all_is_positive.of(All[Derivative > 0])
    assert x == x_
    assert d == 2
    assert domain == _domain == __domain
    assert domain.left_open and domain.right_open
    a, b = domain.of(Interval)
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    f = lambda x: fx._subs(x_, x)
    return is_differentiable(f, x0, x1, open=False)


@prove
def prove(Eq):
    from axiom import calculus, sets

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(Element(x0, domain), Element(x1, domain), All[x:domain](Derivative(f(x), (x, 2)) > 0))

    Eq << calculus.all_gt_zero.imply.is_differentiable.apply(Eq[2])

    Eq << sets.el.el.imply.subset.interval.apply(Eq[0], Eq[1])
    Eq << sets.subset.all.imply.all.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-05-05
# updated on 2020-05-05
