from util import *


@apply
def apply(is_nonzero, is_nonzero_, Y, Y_):
    y = Symbol(integer=True)
    X, x = is_nonzero.of(Unequal[Probability[Equal], 0])
    X_, x_ = is_nonzero_.of(Unequal[Probability[Equal], 0])
    assert x_ == x
    from axiom.stats.imply.sum_ge_zero import KL
    return GreaterEqual(KL(Probability(Equal(X, x) & Equal(Y, y)), Probability(Equal(X_, x) & Equal(Y_, y))),
                        KL(Probability(Equal(X, x)), Probability(Equal(X_, x))))


@prove
def prove(Eq):
    from axiom import stats, algebra

    p, q = Function(shape=(), integer=True)
    X, Y = Symbol(random=True, integer=True)
    X_ = Symbol("X'", random=True, integer=True)
    Y_ = Symbol("Y'", random=True, integer=True)
    x = Symbol(integer=True)
    Eq << apply(Unequal(Probability(Equal(X, x)), 0),
                Unequal(Probability(Equal(X_, x)), 0),
                Y, Y_)

    y = Eq[-1].lhs.variables[-1]
    Eq << stats.ne_zero.imply.eq.bayes.cond.apply(Eq[0], cond=Equal(Y, y))

    Eq << stats.ne_zero.imply.eq.bayes.cond.apply(Eq[1], cond=Equal(Y_, y))

    Eq << Eq[2].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.find(Log).apply(algebra.log.to.add, pivot=2)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.limits.swap)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Probability[Conditioned]]).apply(stats.sum.to.one.conditioned)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.swap)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.separate)

    Eq << stats.imply.sum_ge_zero.conditioned.apply(*Eq[-1].find(Log).arg.of(Expr / Expr))

    Eq << algebra.ge_zero.imply.ge_zero.mul.apply(Eq[-1], Probability(Equal(X, x)))

    Eq << algebra.ge_zero.imply.ge_zero.sum.apply(Eq[-1], (x,))


if __name__ == '__main__':
    run()
# created on 2021-07-23
