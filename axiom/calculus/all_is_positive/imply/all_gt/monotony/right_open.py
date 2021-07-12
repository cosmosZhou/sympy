from util import *


@apply
def apply(given):
    (fx, (x, n)), (_x, domain) = given.of(All[Derivative > 0])
    assert n == 1
    assert not domain.left_open
    assert x == _x

    a, b = domain.args
    return All[x:Interval(a, b, left_open=True, right_open=domain.right_open)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, calculus, sets

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    domain = Interval(a, b, right_open=True)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    t = Symbol.t(real=True)
    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=t < b)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.lt.all.imply.all.limits.restrict)

    Eq << Eq[-1].this.rhs.apply(calculus.all_is_positive.imply.all_gt.monotony.right_close)

    e = Symbol.e(real=True)
    Eq << Eq[-1].subs(t, b - e)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << -Eq[-1].this.lhs

    Eq.suffice = Eq[-1].this.rhs.apply(algebra.all.limits.subs.negate.real, x, b - x)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(algebra.any.limits.subs.negate.real, x, b - x)

    Eq << algebra.any.imply.any_et.limits_cond.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.imply.gt.split.interval)

    eta = Symbol.eta(real=True, positive=True)
    Eq << Eq[-1].this.find(Greater).apply(algebra.is_positive.imply.any_gt, var=eta)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.any.imply.any_et, simplify=None)

    Eq << algebra.any.imply.any.limits.swap.apply(Eq[-1], simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=1)

    Eq << Eq.suffice.subs(e, eta)
    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
