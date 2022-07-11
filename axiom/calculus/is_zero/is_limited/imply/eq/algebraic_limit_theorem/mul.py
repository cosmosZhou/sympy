from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    limited_f = limited_f.of(Equal[0])
    fx, (x, x0, dir) = limited_f.of(Limit)

    gx, (_x, _x0, _dir), R = of_limited(limited_g)

    assert R.is_Interval

    assert dir == _dir

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0:dir](fx * gx), 0)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra
    x, x0 = Symbol(real=True)
    f, g = Function(real=True)

    dir = S.One
    Eq << apply(Equal(Limit[x:x0:dir](f(x)), 0), Element(Limit[x:x0:dir](g(x)), Reals))

    epsilon = Symbol(real=True, positive=True)

    δ_0 = Symbol(real=True, positive=True)

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[0], epsilon, δ_0)

    δ_1 = Symbol(real=True, positive=True)

    Eq << calculus.is_limited.imply.any_all.le.boundedness.apply(Eq[1], delta=δ_1, var='B')

    B = Eq[-1].variables[1]

    assert B > 0
    Eq << Eq[-2].subs(epsilon, epsilon / B)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.lt.imply.lt.abs.mul)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(sets.lt.given.el.interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(sets.lt.given.el.interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[1].simplify()

    delta = Symbol(real=True, positive=True)

    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(δ_0, δ_1), delta)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

# created on 2020-04-10
