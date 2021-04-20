from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete
from axiom.discrete.continued_fraction.HK.definition import HK


@apply
def apply(x, n):
    assert n >= 2
    H, K = HK(x)
    return Equal(H[n] * K[n - 2] - H[n - 2] * K[n], (-1) ** n * x[n])


@prove
def prove(Eq): 
    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    Eq << apply(x, n)    
    
    H = Eq[0].lhs.base
    K = Eq[1].lhs.base
    
    Eq << discrete.continued_fraction.HK.definition.apply(x, n - 1, H, K)
    
    Eq << Eq[2].subs(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << discrete.continued_fraction.HK.recurrence.apply(x, n - 1, H, K)
    
    Eq << Eq[-1] * x[n]
    
    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    prove()

