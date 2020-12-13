from sympy import factorial
from sympy.core.relational import Equality
from sympy.stats.drv import SingleDiscretePSpace
from sympy.stats.drv_types import PoissonDistribution
from sympy.stats.rv import PDF, pspace
from axiom.utility import plausible
from axiom.utility import check
import axiom
from sympy.core.symbol import Symbol
from sympy.sets import NonnegativeIntegers


@plausible
def apply(x0, x1):
    assert x0.is_random and x1.is_random
    pspace0 = pspace(x0)
    pspace1 = pspace(x1)
    if not isinstance(pspace0, SingleDiscretePSpace) or not isinstance(pspace1, SingleDiscretePSpace):
        return None
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, PoissonDistribution) or not isinstance(distribution1, PoissonDistribution):
        return None
    
    Y = Symbol.y(distribution=PoissonDistribution(distribution0.lamda + distribution1.lamda))
    y = pspace(Y).symbol
    
    return Equality(PDF(x0 + x1)(y), PDF(Y)(y).doit())


@check
def prove(Eq):
    assert NonnegativeIntegers.is_extended_negative == False
    assert NonnegativeIntegers.is_extended_nonnegative
    
    lamda0 = Symbol.lamda0(positive=True)
    lamda1 = Symbol.lamda1(positive=True)

    x0 = Symbol.x0(distribution=PoissonDistribution(lamda0))
    x1 = Symbol.x1(distribution=PoissonDistribution(lamda1))

    Eq << apply(x0, x1)

    Eq << Eq[0].lhs.this.doit(evaluate=False)

    Eq << Eq[0].reversed + Eq[-1]

    Eq << Eq[-1].this.rhs.powsimp()

    y = Eq[0].lhs.symbol
    Eq << Eq[-1] * factorial(y)

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(lamda0, lamda1, y)

    Eq << Eq[-2].reversed + Eq[-1]

    Eq << Eq[-1].this.rhs.combsimp()


if __name__ == '__main__':
    prove(__file__)
