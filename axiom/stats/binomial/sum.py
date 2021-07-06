from util import *


@apply
def apply(X0, X1):
    n0, p = pspace(X0).distribution.of(BinomialDistribution)
    n1, _p = pspace(X1).distribution.of(BinomialDistribution)
    
    assert _p == p

    Y = Symbol.y(distribution=BinomialDistribution(n0 + n1, p))
    y = pspace(Y).symbol

    return Equal(Probability(Equal(X0 + X1, y)), Probability(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n0 = Symbol.n0(integer=True, positive=True)
    n1 = Symbol.n1(integer=True, positive=True)
    p = Symbol.p(domain=Interval(0, 1, left_open=True, right_open=True))
    X0 = Symbol.X0(distribution=BinomialDistribution(n0, p))
    X1 = Symbol.X1(distribution=BinomialDistribution(n1, p))
    Eq << apply(X0, X1)

    Eq << Eq[0].lhs.this.doit(evaluate=False)

    Eq << Eq[0].subs(Eq[-1])

    Eq << discrete.combinatorics.binomial.theorem.apply(p, 1, n0)

    Eq << discrete.combinatorics.binomial.theorem.apply(p, 1, n1)

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << discrete.combinatorics.binomial.theorem.apply(p, 1, n0 + n1).subs(Eq[-1])

    Eq << Eq[-1].this.lhs.as_multiple_limits()

    (k, *_), (l, *_) = Eq[-1].lhs.limits
    Eq << Eq[-1].this.lhs.limits_subs(k, k - l)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.swap.intlimit.parallel)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.lhs.apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.rhs.apply(discrete.sum.to.matmul)

    Eq << discrete.vector.independence.matmul_equal.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(k, Eq[0].lhs.arg.rhs)

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, Eq[1].find(Sum).variable)

    Eq << Eq[-1] * Mul(*Eq[0].rhs.args[:-1])


if __name__ == '__main__':
    run()
