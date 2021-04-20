from axiom.utility import prove, apply
from sympy.core.relational import Equal

from sympy.stats.crv_types import NormalDistribution
from sympy.stats.rv import PDF, pspace
from sympy import sqrt
from sympy.stats.crv import SingleContinuousPSpace
from axiom.statistics.guassion import quadratic
from sympy.core.symbol import Symbol
from axiom import algebra

@apply
def apply(x0, x1):
    assert x0.is_random and x1.is_random

    pspace0 = pspace(x0)
    pspace1 = pspace(x1)
    if not isinstance(pspace0, SingleContinuousPSpace) or not isinstance(pspace1, SingleContinuousPSpace):
        return
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, NormalDistribution) or not isinstance(distribution1, NormalDistribution):
        return
    Y = Symbol.y(distribution=NormalDistribution(distribution0.mean + distribution1.mean,
                                            sqrt(distribution0.std * distribution0.std + distribution1.std * distribution1.std)))
    y = pspace(Y).symbol

    return Equal(PDF(x0 + x1)(y), PDF(Y)(y).doit())




@prove
def prove(Eq):

    mu0 = Symbol.mu0(real=True)
    mu1 = Symbol.mu1(real=True)

    sigma0 = Symbol.sigma0(positive=True)
    sigma1 = Symbol.sigma1(positive=True)

    x0 = Symbol.x0(distribution=NormalDistribution(mu0, sigma0))
    x1 = Symbol.x1(distribution=NormalDistribution(mu1, sigma1))    
    assert sqrt(sigma0 * sigma0 + sigma1 * sigma1) > 0
        
    Eq << apply(x0, x1)

    Eq << Eq[0].lhs.this.doit(evaluate=False)

    Eq << Eq[-1].this.rhs.args[-1].args[0].doit()

    Eq << quadratic.apply(Eq[-1].rhs.args[-1])

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[0].this.lhs.subs(Eq[-1])

    Eq << Eq[-1] / Eq[-1].rhs

    Eq << Eq[-1].apply(algebra.eq.given.eq.log)    

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.ratsimp()


# https://www.asmeurer.com/blog/
if __name__ == '__main__':    
    prove()

