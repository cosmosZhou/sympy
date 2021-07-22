from util import *


@apply
def apply(is_limited):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(is_limited, positive=True)
    return Equal(Limit[x:x0:dir](log(fx)), log(Limit[x:x0:dir](fx)))


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Contains(Limit[x:x0](f(x)), Interval(0, oo, left_open=True)))

    epsilon0 = Symbol.epsilon0(positive=True)
    delta0 = Symbol.delta0(positive=True)
    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], epsilon0, delta0, var='A')

    A = Eq[-1].expr.expr.find(Add[-~Symbol])
    Eq.is_limited = A.this.definition.reversed

    Eq << Eq[0].subs(Eq.is_limited)

    Eq.A_is_positive = sets.contains.imply.is_positive.apply(Eq[-1])

    Eq << algebra.is_positive.eq.imply.eq.log.apply(Eq.A_is_positive, Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << sets.contains.imply.is_nonzero.apply(Eq[0])

    delta = Symbol.delta(positive=True)
    epsilon = Symbol.epsilon(positive=True)
    Eq << Eq[-2].this.apply(calculus.eq.to.any_all.limit_definition, delta=delta, epsilon=epsilon)

    Eq << Eq[-1].this.expr.expr.lhs.arg.apply(algebra.add.to.log)

    Eq << Eq[2].this.expr.expr.apply(algebra.lt.imply.et.split.abs)

    Eq << Eq[-1].this.expr.expr.args[0].apply(algebra.lt.transposition, lhs=0)

    Eq << Eq[-1].this.expr.expr.args[0].apply(algebra.gt.transposition, lhs=0)

    Eq << Eq[-1].this.expr.expr.apply(sets.lt.gt.imply.contains.interval)

    Eq << algebra.cond.any_all.imply.any_all_et.apply(Eq.A_is_positive, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(sets.is_positive.contains.imply.contains.div)

    Eq << Eq[-1].this.expr.expr.rhs.args[0].apply(algebra.mul.to.add)

    Eq << Eq[-1].this.expr.expr.rhs.args[1].apply(algebra.mul.to.add)

    epsilon1 = Symbol.epsilon1(domain=Interval(0, 1, left_open=True, right_open=True))
    Eq << algebra.cond.imply.ou.subs.apply(Eq[-1], epsilon0, epsilon1 * A)

    Eq << algebra.cond.ou.imply.cond.apply(Eq.A_is_positive * epsilon1, Eq[-1])


if __name__ == '__main__':
    run()