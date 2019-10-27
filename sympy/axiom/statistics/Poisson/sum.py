from sympy import exp, Symbol
from sympy import factorial
from sympy.core.relational import Equality
from sympy.stats.drv import SingleDiscretePSpace
from sympy.stats.drv_types import Poisson, PoissonDistribution
from sympy.stats.rv import Density, RandomSymbol
from sympy.utility import plausible
from sympy.utility import check
from sympy import axiom


def apply(x0, x1):
    if not isinstance(x0, RandomSymbol) or not isinstance(x1, RandomSymbol):
        return None
    pspace0 = x0.pspace
    pspace1 = x1.pspace
    if not isinstance(pspace0, SingleDiscretePSpace) or not isinstance(pspace1, SingleDiscretePSpace):
        return None
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, PoissonDistribution) or not isinstance(distribution1, PoissonDistribution):
        return None
    y = Symbol("y", integer=True, nonnegative=True)
    lamda = distribution0.lamda + distribution1.lamda
    return Equality(Density(x0 + x1)(y), exp(-lamda) * lamda ** y / factorial(y),
                    plausible=plausible())


@check
def prove(Eq):

    lamda0 = Symbol("lamda0", positive=True)
    lamda1 = Symbol("lamda1", positive=True)

    x0 = Poisson('x0', lamda0)
    x1 = Poisson('x1', lamda1)

    Eq << apply(x0, x1)

    Eq << Equality.by_definition_of(Density(x0 + x1))

    Eq << Eq[-1].this.rhs.args[-1].function.args[-1].doit(deep=False)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.rhs.powsimp()

    y = Eq[0].lhs.symbol
    Eq << Eq[-1] * factorial(y)

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(lamda0, lamda1, y)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.combsimp()


if __name__ == '__main__':
    prove(__file__)
