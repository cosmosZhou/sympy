from util import *
import axiom


@apply
def apply(X0, X1):
    from sympy.stats.rv import PDF
    if not X0.is_random or not X1.is_random:
        return
    pspace0 = pspace(X0)
    pspace1 = pspace(X1)
    if not pspace0.is_SingleDiscretePSpace or not pspace1.is_SingleDiscretePSpace:
        return
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, BinomialDistribution) or not isinstance(distribution1, BinomialDistribution):
        return
    if distribution0.p != distribution1.p:
        return

    Y = Symbol.y(distribution=BinomialDistribution(distribution0.n + distribution1.n, distribution0.p))
    y = pspace(Y).symbol

    return Equal(PDF(X0 + X1)(y), PDF(Y)(y).doit())


@prove
def prove(Eq):
    from axiom import discrete
    n0 = Symbol.n0(integer=True, positive=True)
    n1 = Symbol.n1(integer=True, positive=True)

    p = Symbol.p(domain=Interval(0, 1, left_open=True, right_open=True))

    X0 = Symbol.X0(distribution=BinomialDistribution(n0, p))
    X1 = Symbol.X1(distribution=BinomialDistribution(n1, p))

    Eq << apply(X0, X1)

    Eq << Eq[0].lhs.this.doit(evaluate=False)

    Eq << Eq[-1].this.rhs.function.powsimp()

    Eq << Eq[0].subs(Eq[-1])

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n0)

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n1)

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n0 + n1).subs(Eq[-1])

    Eq << Eq[-1].this.lhs.as_multiple_limits()

    (k, *_), (l, *_) = Eq[-1].lhs.limits
    Eq << Eq[-1].this.lhs.limits_subs(k, k - l)

    Eq << Eq[-1].this.lhs.as_separate_limits()

    Eq << Eq[-1].this.lhs.astype(MatMul)

    Eq << Eq[-1].this.rhs.astype(MatMul)

    Eq << discrete.vector.independence.matmul_equal.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(k, Eq[0].lhs.symbol)

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, Eq[1].rhs.variable)

    Eq << Eq[-1] * Mul(*Eq[0].rhs.args[:-1])

    y = Eq[0].lhs.symbol
    p = Symbol.p(Probability(Equal(X0 + X1, y)))
    Eq << p.this.definition

    Eq << Eq[-1].this.rhs.doit()


if __name__ == '__main__':
    run()
