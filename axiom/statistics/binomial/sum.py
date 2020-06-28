
from sympy import Symbol
import axiom
from sympy.core.relational import Equality
from sympy.stats.drv import SingleDiscretePSpace
from sympy.stats.drv_types import BinomialDistribution, Binomial
from sympy.stats.rv import Density, RandomSymbol
from sympy.utility import check
from sympy.utility import plausible

from sympy import Interval
from axiom import Algebre
# sys.getrecursionlimit()
# print('sys.getrecursionlimit() =', sys.getrecursionlimit())
# sys.setrecursionlimit(100000000)


@plausible
def apply(x0, x1):
    if not isinstance(x0, RandomSymbol) or not isinstance(x1, RandomSymbol):
        return None
    pspace0 = x0.pspace
    pspace1 = x1.pspace
    if not isinstance(pspace0, SingleDiscretePSpace) or not isinstance(pspace1, SingleDiscretePSpace):
        return None
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, BinomialDistribution) or not isinstance(distribution1, BinomialDistribution):
        return None
    if distribution0.p != distribution1.p:
        return None

    Y = Binomial('y', distribution0.n + distribution1.n, distribution0.p)
    y = Y.symbol

    return Equality(Density(x0 + x1)(y), Density(Y)(y).doit())


@check
def prove(Eq):
    n0 = Symbol("n0", integer=True, positive=True)
    n1 = Symbol("n1", integer=True, positive=True)
    
    y = Symbol("y", integer=True, nonnegative=True)
#     y = Symbol("y", domain=Interval(0, n0 + n1, integer=True))    

    from sympy.functions.elementary.miscellaneous import Min, Max
    from sympy.core.numbers import oo
    lhs = y + 1
    rhs = Max(-1, -n0 + y - 1)
    assert lhs > rhs
    
    lhs = Min(n1 + 1, y + 1)
    rhs = Min(n1, Max(-1, -n0 + y - 1))    
    assert lhs > rhs
    
    mini = Min(n1, Max(-1, -n0 + y - 1))
    print(mini < 0)    
    union = Interval(Max(0, -n0 + y), Min(n1, y), integer=True)
    univeralSet = Interval(-oo, oo, integer=True)
    domain = Interval(0, n1, integer=True)

    complement = univeralSet - union
    print(complement)
    print(complement & domain)

    p = Symbol("p", domain=Interval(0, 1))

    x0 = Binomial('x0', n0, p)
    x1 = Binomial('x1', n1, p)

    Eq << apply(x0, x1)

    Eq << Equality.by_definition_of(Density(x0 + x1))

#     Eq << Eq[-1].this.rhs.function.args[3].doit(deep=False)

    Eq << Eq[-1].this.rhs.function.powsimp()

    Eq.convolution = Eq[-1].subs(Eq[0])

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n0)
    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n1)

    Eq << Eq[-1] * Eq[-2]
    Eq << Eq[-1].this.lhs.powsimp()
    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n0 + n1).subs(Eq[-1])

    Eq << Eq[-1].this.lhs.as_multiple_limits()

    (k, *_), (l, *_) = Eq[-1].this.lhs.limits
    Eq << Eq[-1].this.lhs.subs(k, k - l)

    Eq << Eq[-1].this.lhs.as_separate_limits()

    Eq << Eq[-1].as_two_terms()
    
    Eq << Algebre.vector.independence.matmul_equality.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(k, y)
    
    Eq << Eq[-1].subs(Eq.convolution)
#     Eq << Eq[-1][Eq[0].lhs.symbol].subs(Eq[3])


if __name__ == '__main__':
    prove(__file__)
