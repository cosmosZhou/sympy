from util import *


@apply
def apply(is_positive, x0, x1):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2
    domain = x_.domain
    assert x0.domain == domain == x1.domain
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    f = lambda x: fx._subs(x_, x)
    x0, x1 = Min(x0, x1), Max(x0, x1)
    return is_differentiable(f, x0, x1, open=False)


@prove
def prove(Eq):
    from axiom import calculus, sets

    a, b = Symbol(real=True)
    f = Function(real=True)
    x, x0, x1 = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    Eq << apply(Derivative(f(x), (x, 2)) > 0, x0, x1)

    Eq << calculus.is_positive.imply.is_differentiable.within.apply(Eq[0], x0, x1, x=Eq[1].variable)

    Eq << calculus.is_positive.imply.is_differentiable.within.apply(Eq[0], x1, x0, x=Eq[1].variable)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.find(Union).apply(sets.union.to.interval)


if __name__ == '__main__':
    run()
