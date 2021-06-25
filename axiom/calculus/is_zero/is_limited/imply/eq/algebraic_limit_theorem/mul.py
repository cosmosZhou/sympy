from util import *


@apply
def apply(*given):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    limited_f, limited_g = given
    limited_f = limited_f.of(Equal[0])
    fx, (x, x0, dir) = limited_f.of(Limit)

    gx, (_x, _x0, _dir) = of_limited(limited_g)
    assert dir == _dir

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0:dir](fx * gx), 0)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)

    dir = S.One
    Eq << apply(Equal(Limit[x:x0:dir](f(x)), 0), Contains(Limit[x:x0:dir](g(x)), Reals))

    ε = Symbol.ε(real=True, positive=True)

    δ0 = Symbol.δ_0(real=True, positive=True)

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[0], ε, δ0)

    δ1 = Symbol.δ_1(real=True, positive=True)

    Eq << calculus.is_limited.imply.any_all.le.boundedness.apply(Eq[1], δ=δ1, var='B')

    B = Eq[-1].variables[1]

    assert B > 0
    Eq << Eq[-2].subs(ε, ε / B)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.abs.mul)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[1].simplify()

    δ = Symbol.δ(real=True, positive=True)

    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(δ0, δ1), δ)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

