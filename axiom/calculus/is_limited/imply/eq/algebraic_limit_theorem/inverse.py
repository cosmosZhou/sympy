from util import *


@apply
def apply(is_limited):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(is_limited, nonzero=True)

    return Equal(Limit[x:x0:dir](1 / fx), 1 / is_limited.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    g = Function.g(real=True)
    Eq << apply(Contains(Limit[x:x0](g(x)), Reals - {0}))

    epsilon0 = Symbol.epsilon_0(real=True, positive=True)
    delta0 = Symbol.delta_0(real=True, positive=True)
    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], epsilon0, delta0, var='A')

    A = Eq[-1].function.function.find(Add[-~Symbol])
    Eq.is_limited = A.this.definition.reversed

    Eq.is_nonzero_real = Eq[0].subs(Eq.is_limited)

    Eq << sets.contains.imply.is_nonzero.apply(Eq.is_nonzero_real)

    Eq << algebra.is_nonzero.eq.imply.eq.inverse.apply(Eq[-1], Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.is_limited)

    delta = Symbol.delta(positive=True)
    epsilon = Symbol.epsilon(positive=True)
    Eq << Eq[-2].this.apply(calculus.eq.to.any_all.limit_definition, delta=delta, epsilon=epsilon)

    delta1 = Symbol.delta1(positive=True)
    Eq << calculus.contains.eq.imply.any_all.lt.half.apply(Eq.is_nonzero_real, Eq.is_limited, delta=delta1)

    Eq.A_is_positive = sets.contains.imply.is_positive.abs.apply(Eq.is_nonzero_real)

    Eq << algebra.cond.any_all.imply.any_all_et.apply(Eq.A_is_positive / 2, Eq[-1])

    Eq << Eq[-1].this.function.function.apply(algebra.is_positive.gt.imply.lt.inverse)

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq.A_is_positive)

    Eq << algebra.cond.any_all.imply.any_all_et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.function.function.apply(algebra.is_positive.lt.imply.lt.mul)

    Eq << algebra.any_all.any_all.imply.any_all_et.limits_intersect.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.mul)

    Eq << Eq[-1].this.find(Mul[Abs]).apply(algebra.mul.to.abs)

    Eq << Eq[-1].this.find(Abs[~Mul]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.function.function.lhs.apply(algebra.abs.neg)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains.interval)

    Eq << Eq[-1].this.function.limits[0][1].args[1].simplify()

    Eq << algebra.cond.imply.ou.subs.apply(Eq[-1], epsilon0, abs(A) ** 2 / 2 * epsilon)

    Eq << algebra.is_positive.imply.is_positive.square.apply(Eq.A_is_positive) * epsilon / 2

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(delta0, delta1), delta)


if __name__ == '__main__':
    run()