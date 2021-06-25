from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir), domain = of_limited(limited_f)

    R = domain | {0}
    assert R.is_UniversalSet

    gx, (_x, _x0, _dir) = of_limited(limited_g)
    assert dir == _dir

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0:dir](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)

    dir = S.One
    Eq << apply(Contains(Limit[x:x0:dir](f(x)), Reals // {0}), Contains(Limit[x:x0:dir](g(x)), Reals))

    ε = Symbol.ε(real=True, positive=True)

    ε0 = Symbol.ε_0(real=True, positive=True)
    δ0 = Symbol.δ_0(real=True, positive=True)

    Eq.limit_A_definition = calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], ε0, δ0, var='A')

    A = -Eq.limit_A_definition.function.function.lhs.arg.args[0]

    Eq << Eq[0].subs(A.this.definition.reversed)

    Eq.is_positive = sets.contains.imply.is_positive.abs.apply(Eq[-1])

    ε1 = Symbol.ε_1(real=True, positive=True)
    δ1 = Symbol.δ_1(real=True, positive=True)

    Eq.limit_B_definition = calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[1], ε1, δ1, var='B')

    B = -Eq.limit_B_definition.function.function.lhs.arg.args[0]

    Eq << algebra.imply.le.abs.add.mul.apply(f(x), g(x), A, B)

    δ2 = Symbol.δ_2(real=True, positive=True)
    Eq << calculus.is_limited.imply.any_all.le.boundedness.apply(Eq[1], δ=δ2, var='B')

    B = Eq[-1].function.function.rhs

    Eq.le = Eq[-1].this.function.function.apply(algebra.le.lt.imply.le.subs, Eq[-2])

    assert B > 0
    Eq << Eq.limit_A_definition.subs(ε0, ε / B / 2)

    Eq.lt_fx = Eq[-1].this.function.function * B

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq.is_positive, ε / 2, simplify=None)

    Eq << Eq.limit_B_definition.subs(ε1, Eq[-1].lhs)

    Eq << Eq[-1].this.function.function.apply(algebra.is_positive.lt.imply.lt.mul, Eq.is_positive)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[-1], Eq.lt_fx)

    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.add)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq.le, Eq[-1])

    Eq << Eq[-1].this.function.function.apply(algebra.lt.le.imply.lt.transit)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[1].simplify()

    δ = Symbol.δ(real=True, positive=True)

    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(δ0, δ1, δ2), δ)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].definition


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

