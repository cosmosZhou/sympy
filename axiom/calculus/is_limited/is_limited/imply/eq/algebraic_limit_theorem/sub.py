from util import *


@apply
def apply(*given):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    limited_f, limited_g = given
    fx, (x, x0, dir) = of_limited(limited_f, real=True)

    gx, (_x, _x0, _dir) = of_limited(limited_g, real=True)
    assert dir == _dir

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0:dir](fx - gx), limited_f.lhs - limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol.x(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Contains(Limit[x:oo](f(x)), Reals), Contains(Limit[x:oo](g(x)), Reals))

    ε = Symbol.ε(real=True, positive=True)
    ε0 = Symbol.ε_0(real=True, positive=True)
    N0 = Symbol.N_0(real=True, positive=True)
    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], ε0, N0, var='A')

    Eq << Eq[-1].subs(ε0, ε / 2)

    ε1 = Symbol.ε_1(real=True, positive=True)
    N1 = Symbol.N_1(real=True, positive=True)
    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[1], ε1, N1, var='B')

    Eq << Eq[-1].subs(ε1, ε / 2)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.abs.sub)

    Eq << Eq[-1].this.function.limits[0][1].apply(algebra.gt.gt.given.gt)

    N = Symbol.N(real=True, positive=True)
    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Max(N0, N1), N)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].args[1].definition


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties
