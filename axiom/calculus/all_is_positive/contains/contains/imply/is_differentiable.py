from util import *


@apply
def apply(all_is_positive, contains0, contains1):
    (fx, (x, d)), (x_, domain) = all_is_positive.of(All[Derivative > 0])
    assert x == x_
    assert d == 2
    assert domain.left_open and domain.right_open    
    x0, domain_ = contains0.of(Contains)
    assert domain_ == domain

    x1, domain_ = contains1.of(Contains)
    assert domain_ == domain

    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    f = lambda x: fx._subs(x_, x)
    return is_differentiable(f, x0, x1, open=False)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    x0 = Symbol.x0(real=True)
    x1 = Symbol.x1(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:domain](Derivative(f(x), (x, 2)) > 0), Contains(x0, domain), Contains(x1, domain))

    Eq << calculus.all_is_positive.imply.is_differentiable.apply(Eq[0])

    x0_ = Symbol.x0(domain=domain)
    x1_ = Symbol.x1(domain=domain)
    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], domain=Interval(x0_, x1_))

    Eq << Eq[-1].subs(x1_, x1)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].subs(x0_, x0)
    Eq << algebra.cond.ou.imply.cond.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
