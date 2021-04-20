from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete
from axiom.discrete.continued_fraction.HK.definition import H, K


@apply
def apply(x, n):
    assert x.is_positive
    assert n > 0    
    return Equal(K(x[1:n + 1]) / H(x[1:n + 1]), H(x[:n + 1]) / K(x[:n + 1]) - x[0])


@prove
def prove(Eq): 
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(x, n)    

    Eq << discrete.continued_fraction.alpha.HK.provided.is_positive.apply(x[:n + 1])
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << discrete.continued_fraction.alpha.HK.provided.is_positive.apply(x[1:n + 1])
    
    Eq << algebra.eq.eq.imply.eq.subs.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1] - x[0]

    
if __name__ == '__main__':
    prove()

