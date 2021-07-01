from util import *


@apply
def apply(given):
    (fx, (x, n)), (_x, a, b) = given.of(All[Derivative > 0])
    assert n == 1
    assert x == _x
    
    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    domain = Interval(a, b)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))
    
    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[0], Interval(a, b, left_open=True, right_open=True))
    
    Eq << Eq[-1].this.function.apply(sets.is_positive.imply.is_real)
    
    Eq << calculus.lt.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()