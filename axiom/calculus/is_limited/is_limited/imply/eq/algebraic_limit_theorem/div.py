from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(limited_f, real=True)
    assert dir == 0
    gx, (_x, _x0, dir) = of_limited(limited_g, nonzero=True)
    assert dir == 0

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0](fx / gx), limited_f.lhs / limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Contains(Limit[x:x0](f(x)), Reals), Contains(Limit[x:x0](g(x)), Reals - {0}))

    Eq.inverse = calculus.is_limited.imply.eq.algebraic_limit_theorem.inverse.apply(Eq[1])

    Eq << sets.contains.imply.is_real.inverse.apply(Eq[1])

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq.inverse, Eq[-1], reverse=True)

    Eq << calculus.is_limited.is_limited.imply.eq.algebraic_limit_theorem.mul.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].subs(Eq.inverse)


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

