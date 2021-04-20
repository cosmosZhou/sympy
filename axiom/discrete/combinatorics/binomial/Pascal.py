from axiom.utility import prove, apply

from sympy import *
from axiom import discrete, algebra


@apply
def apply(n, k):
    return Equal(binomial(n, k), binomial(n - 1, k) + binomial(n - 1, k - 1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    k = Symbol.k(domain=Interval(1, n - 1, integer=True))
    
    Eq << apply(n, k)

    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.find(binomial).definition
    
    Eq << Eq[-1].this.find(binomial).definition
    
    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)

    Eq << Eq[-1] / factorial(n - 1)
    
    Eq << Eq[-1] * factorial(k)
    
    Eq << Eq[-1] * factorial(n - k)
    
    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)
    
    Eq << Eq[-1].this.rhs.ratsimp()
    
    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)


if __name__ == '__main__':
    prove()
