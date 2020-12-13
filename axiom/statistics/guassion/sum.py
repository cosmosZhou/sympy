from axiom.utility import plausible
from sympy.core.relational import Equality

from sympy.stats.crv_types import NormalDistribution
from sympy.stats.rv import PDF, pspace
from sympy import sqrt
from sympy.stats.crv import SingleContinuousPSpace
from axiom.statistics.guassion import quadratic
from sympy.core.symbol import Symbol

@plausible
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

    return Equality(PDF(x0 + x1)(y), PDF(Y)(y).doit())


from axiom.utility import check


@check
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

    Eq << Eq[-1].log()

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.ratsimp()


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
# python run.py axiom.statistics.guassion.sum axiom.calculus.trigonometry.sine.wallis axiom.discrete.combinatorics.permutation.adjacent.swapn.permutation axiom.statistics.bayes.argmax axiom.discrete.combinatorics.permutation.index.indexOf_indexed axiom.discrete.combinatorics.permutation.adjacent.swap2.general axiom.neuron.bilinear.transpose axiom.sets.contains.imply.equality.piecewise axiom.sets.equality.imply.equality.permutation axiom.statistics.die.expectation axiom.statistics.guassion.quadratic axiom.discrete.kronecker_delta.concatenate01 axiom.sets.forall_contains.forall_contains.forall_equality.imply.equality axiom.statistics.bayes.is_nonzero.et axiom.statistics.bayes.is_nonzero.is_nonzero.slice axiom.algebre.vector.cosine_similarity axiom.sets.contains.imply.equality.equality1 axiom.sets.equality.imply.exists_equality.size_deduction axiom.statistics.bayes.equality.equality.product axiom.calculus.integral.intermediate_value_theorem axiom.sets.forall_et.imply.forall_inequality axiom.sets.contains.contains.imply.subset axiom.statistics.bayes.theorem axiom.sets.is_emptyset.imply.notcontains axiom.sets.notcontains.imply.notcontains.union_comprehension axiom.sets.supset.imply.supset axiom.algebre.is_nonzero.is_nonzero.imply.is_nonzero axiom.sets.contains.imply.equality.union axiom.sets.contains.imply.equality.intersection axiom.sets.forall_contains.forall_contains.imply.equality axiom.sets.contains.imply.exists_contains axiom.sets.equality.imply.subset axiom.sets.equality.imply.supset    
    prove(__file__)

