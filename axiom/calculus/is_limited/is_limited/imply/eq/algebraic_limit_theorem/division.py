from util import *


@apply
def apply(*given):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    limited_f, limited_g = given
    fx, (x, x0, dir) = of_limited(limited_f)
    assert dir == 0
    gx, (_x, _x0, dir) = of_limited(limited_g)
    assert dir == 0

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0](fx + gx), limited_f.lhs + limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(Contains(Limit[x:x0](f(x)), Reals), Contains(Limit[x:x0](g(x)), Reals))

    ε = Symbol.ε(real=True, positive=True)

    ε0 = Symbol.ε_0(real=True, positive=True)
    δ0 = Symbol.δ_0(real=True, positive=True)

    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], ε0, δ0, var='A')
    Eq << Eq[-1].subs(ε0, ε / 2)

    ε1 = Symbol.ε_1(real=True, positive=True)
    δ1 = Symbol.δ_1(real=True, positive=True)

    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[1], ε1, δ1, var='B')
    Eq << Eq[-1].subs(ε1, ε / 2)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.abs.add)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[1].simplify()

    δ = Symbol.δ(real=True, positive=True)

    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(δ0, δ1), δ)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].definition


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

