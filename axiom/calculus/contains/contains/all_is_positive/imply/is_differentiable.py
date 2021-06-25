from util import *


@apply
def apply(contains0, contains1, all_is_positive):
    x0, _domain = contains0.of(Contains)
    x1, __domain = contains1.of(Contains)
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

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    x1 = Symbol.x1(real=True)
    f = Function.f(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(Contains(x0, domain), Contains(x1, domain), All[x:domain](Derivative(f(x), (x, 2)) > 0))

    Eq << calculus.all_is_positive.imply.is_differentiable.apply(Eq[2])

    Eq << sets.contains.contains.imply.subset.interval.apply(Eq[0], Eq[1])
    Eq << sets.subset.all.imply.all.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()