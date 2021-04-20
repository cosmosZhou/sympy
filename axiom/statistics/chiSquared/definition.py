from sympy import *
from axiom.utility import prove, apply
from sympy.stats.crv_types import ChiSquaredDistribution, NormalDistribution    
from sympy.stats.rv import PDF, pspace
from axiom import calculus, statistics


@apply
def apply(X, Y):
    i = Symbol.i(integer=True)

    assert Y.is_random and X.is_random
    y = pspace(Y).symbol
    assert y >= 0
    assert not y.is_random
    assert isinstance(Y.distribution, ChiSquaredDistribution)
    k = Y.distribution.k
    assert Sum[i:k](X[i] * X[i]).is_random
    
    return Equal(PDF(Sum[i:k](X[i] * X[i]))(y), PDF(Y)(y).doit())




@prove
def prove(Eq):
    i = Symbol.i(integer=True, nonnegative=True)
    X = Symbol.X(shape=(oo,), distribution=NormalDistribution(0, 1))
    assert X[i].is_extended_real
    assert X.is_random

    k = Symbol.k(integer=True, positive=True)
    Y = Symbol.Y(distribution=ChiSquaredDistribution(k))
    assert Y.is_extended_real
    assert Y.is_random    

    Eq << apply(X, Y)

    Eq << statistics.chiSquared.induction.apply(Symbol.Y(LAMBDA[k](Sum[i:k](X[i] * X[i]))), Y)    
    
    Eq << Eq[-1].this.lhs.args[0].args[0].definition


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    prove()
