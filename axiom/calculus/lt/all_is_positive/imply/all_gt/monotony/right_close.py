from util import *


@apply
def apply(lt, given):
    a, b = lt.of(Less)
    (fx, (x, n)), (_x, _a, _b) = given.of(All[Derivative > 0])
    assert a == _a and b == _b
    assert n == 1
    assert x == _x

    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import sets, calculus, algebra

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    domain = Interval(a, b)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    Eq << apply(a < b, All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[1].this.expr.apply(sets.is_positive.imply.is_real)

    Eq.is_continuous = calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])

    Eq.is_differentiable = algebra.all.imply.all.limits.restrict.apply(Eq[-1], Interval(a, b, left_open=True, right_open=True))

    t = Symbol.t(real=True)
    Eq.le = Contains(t, Interval(a, b, left_open=True)).this.apply(sets.contains.imply.le.split.interval)

    Eq <<= algebra.cond.suffice.imply.suffice.et.rhs.apply(Eq.is_continuous, Eq.le), algebra.cond.suffice.imply.suffice.et.rhs.apply(Eq.is_differentiable, Eq.le)

    Eq <<= Eq[-2].this.rhs.apply(algebra.le.all.imply.all.limits.restrict), Eq[-1].this.rhs.apply(algebra.le.all.imply.all.limits.restrict)

    Eq <<= Contains(t, Interval(a, b, left_open=True)).this.apply(sets.contains.imply.lt.split.interval) & Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(calculus.lt.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(algebra.any.imply.any_et.limits.cond, simplify=None)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.imply.is_nonemptyset, simplify=None)

    Eq.any = Eq[-1].this.rhs.find(Unequal).apply(sets.interval_is_nonemptyset.imply.is_positive, simplify=None)

    Eq << algebra.cond.suffice.imply.suffice.et.rhs.apply(Eq[1], Eq.le)

    Eq << Eq[-1].this.rhs.apply(algebra.le.all.imply.all.limits.restrict)

    Eq << Eq[-1].this.find(All).apply(algebra.all.imply.all.limits.restrict, Interval(a, t, left_open=True, right_open=True))

    Eq <<= Eq.any & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.all.any.imply.any_et)

    Eq << Eq[-1].this.rhs.apply(algebra.any_et.imply.any.limits_absorb, index=1)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.is_positive.is_positive.imply.is_positive)

    Eq << Eq[-1].this.rhs.apply(algebra.any.imply.any_et.limits.unleash)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.gt.eq.imply.gt.transit)

    Eq << algebra.suffice.imply.suffice.split.et.apply(Eq[-1], 1)

    Eq << algebra.suffice.imply.all.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.is_positive.imply.gt)


if __name__ == '__main__':
    run()