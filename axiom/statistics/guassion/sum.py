from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.stats.crv_types import NormalDistribution, Normal
from sympy.stats.rv import Density, RandomSymbol
from sympy import sqrt
from sympy.stats.crv import SingleContinuousPSpace
from axiom.statistics.guassion import quadratic
from sympy.core.symbol import Symbol


@plausible
def apply(x0, x1):
    if not isinstance(x0, RandomSymbol) or not isinstance(x1, RandomSymbol):
        return None
    pspace0 = x0.pspace
    pspace1 = x1.pspace
    if not isinstance(pspace0, SingleContinuousPSpace) or not isinstance(pspace1, SingleContinuousPSpace):
        return None
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, NormalDistribution) or not isinstance(distribution1, NormalDistribution):
        return None
    Y = Normal('y', distribution0.mean + distribution1.mean, sqrt(distribution0.std * distribution0.std + distribution1.std * distribution1.std))
    y = Y.symbol

    return Equality(Density(x0 + x1)(y), Density(Y)(y).doit())


from sympy.utility import check


@check
def prove(Eq):

    mu0 = Symbol("mu0", real=True)
    mu1 = Symbol("mu1", real=True)

    sigma0 = Symbol("sigma0", positive=True)
    sigma1 = Symbol("sigma1", positive=True)

    x0 = Normal('x0', mu0, sigma0)
    x1 = Normal('x1', mu1, sigma1)

    Eq << apply(x0, x1)

    Eq << Equality.by_definition_of(Density(x0 + x1))

    Eq << Eq[-1].this.rhs.args[-1].args[0].doit()

    Eq << quadratic.apply(Eq[-1].rhs.args[-1])

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[0].this.lhs.subs(Eq[-1])

    Eq << Eq[-1] / Eq[-1].rhs

    Eq << Eq[-1].log()

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.ratsimp()


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    prove(__file__)

