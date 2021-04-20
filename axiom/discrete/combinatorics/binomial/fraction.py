from sympy import *
from axiom.utility import prove, apply
from axiom import discrete


@apply
def apply(n, k):
    return Equal(Binomial(n, k) / n, Binomial(n - 1, k) / (n - k))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    
    Eq << apply(n, k)
    
    Eq << Eq[-1].this.find(binomial).definition
    
    Eq << Eq[-1].this.find(binomial).definition
    
    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)
    
    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)


if __name__ == '__main__':
    prove()
