from util import *


@apply
def apply(all_is_positive, contains0, contains1, le):
    (fx, (x, d)), (x_, domain) = all_is_positive.of(All[Derivative > 0])
    assert x == x_
    assert d == 1
    assert domain.left_open and domain.right_open    
    x0, domain_ = contains0.of(Contains)
    assert domain_ == domain

    x1, domain_ = contains1.of(Contains)
    assert domain_ == domain
    
    _x0, _x1 = le.of(Less)
    assert x0 == _x0
    assert x1 == _x1

    f = lambda x: fx._subs(x_, x)
    return f(x0) < f(x1)


@prove
def prove(Eq):
    from axiom import sets, calculus, algebra

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    x0 = Symbol.x0(real=True)
    x1 = Symbol.x1(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0), Contains(x0, domain), Contains(x1, domain), x0 < x1)

    Eq << Eq[0].this.function.apply(sets.gt.imply.contains.reals)

    Eq.subset = sets.contains.contains.imply.subset.interval.apply(Eq[1], Eq[2])

    Eq << sets.subset.all.imply.all.apply(Eq.subset, Eq[-1])

    Eq << calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])

    Eq << algebra.lt.imply.le.relaxed.apply(Eq[3])

    Eq.any = calculus.le.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.closed.apply(Eq[-1], Eq[-2], Eq[-3])

    Eq << sets.subset.all.imply.all.apply(Eq.subset, Eq[0])

    Eq << algebra.lt.imply.is_positive.apply(Eq[3])

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.function.apply(algebra.is_positive.is_positive.imply.is_positive)

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq.any)

    Eq << Eq[-1].this.function.apply(algebra.gt.eq.imply.gt.transit)

    Eq << algebra.is_positive.imply.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()