from util import *


@apply
def apply(is_positive, x0, x1, x=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2
    domain = x_.domain
    assert x0.domain == domain == x1.domain
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    f = lambda x: fx._subs(x_, x)
    return is_differentiable(f, x0, x1, open=False, x=x)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a, b = Symbol(real=True)
    f = Function(real=True)

    x, x0, x1 = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    Eq << apply(Derivative(f(x), (x, 2)) > 0, x0, x1)

    Eq << algebra.cond.imply.all.apply(Eq[0], x)

    Eq << calculus.all_is_positive.imply.is_differentiable.apply(Eq[-1])

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], domain=Interval(x0, x1))


if __name__ == '__main__':
    run()
