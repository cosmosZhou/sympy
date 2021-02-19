from sympy import *
import axiom
from sympy.stats.drv import SingleDiscretePSpace
from sympy.stats.drv_types import BinomialDistribution
from sympy.stats.rv import pspace, PDF
from axiom.utility import prove, apply

from axiom import discrete


@apply
def apply(x0, x1):
    if not x0.is_random or not x1.is_random:
        return
    pspace0 = pspace(x0)
    pspace1 = pspace(x1)
    if not isinstance(pspace0, SingleDiscretePSpace) or not isinstance(pspace1, SingleDiscretePSpace):
        return
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, BinomialDistribution) or not isinstance(distribution1, BinomialDistribution):
        return
    if distribution0.p != distribution1.p:
        return

    Y = Symbol.y(distribution=BinomialDistribution(distribution0.n + distribution1.n, distribution0.p))
    y = pspace(Y).symbol

    return Equality(PDF(x0 + x1)(y), PDF(Y)(y).doit())


@prove
def prove(Eq):
    n0 = Symbol.n0(integer=True, positive=True)
    n1 = Symbol.n1(integer=True, positive=True)
    
    y = Symbol.y(integer=True, nonnegative=True)

    lhs = y + 1
    rhs = Max(-1, -n0 + y - 1)
    assert lhs > rhs
    
    lhs = Min(n1 + 1, y + 1)
    rhs = Min(n1, Max(-1, -n0 + y - 1))    
    assert lhs > rhs
    
    p = Symbol.p(domain=Interval(0, 1, left_open=True, right_open=True))

    assert p.is_nonzero
    assert (1 - p).is_nonzero
    
    x0 = Symbol.x0(distribution=BinomialDistribution(n0, p)) 
    x1 = Symbol.x1(distribution=BinomialDistribution(n1, p))

    Eq << apply(x0, x1)
    
    assert Eq[0].rhs.args[0].is_nonzero and Eq[0].rhs.args[1].is_nonzero
    assert x0.is_integer and x1.is_integer
    
    Eq << Eq[0].lhs.this.doit(evaluate=False)
    
    Eq << Eq[-1].this.rhs.function.powsimp()
    
    Eq << Eq[-1] + Eq[0].reversed    
    
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
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)
