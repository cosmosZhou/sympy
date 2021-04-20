from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete
from axiom.discrete.continued_fraction.HK.definition import HK


@apply
def apply(x, n, H=None, K=None):
    assert n > 0
    if H is None or K is None:
        H, K = HK(x)
        
    return Equal(H[n] * K[n - 1] - H[n - 1] * K[n], (-1) ** (n + 1))


@prove
def prove(Eq): 
    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)
    
    Eq << apply(x, n)
    
    H = Eq[0].lhs.base
    K = Eq[1].lhs.base
    Eq.initial = Eq[-1].subs(n, 1)
    
    Eq << H[0].this.definition.this.rhs.definition

    Eq << H[1].this.definition.this.rhs.definition
    
    Eq << K[0].this.definition.this.rhs.definition
    
    Eq << K[1].this.definition.this.rhs.definition
    
    Eq << Eq.initial.subs(Eq[-4], Eq[-3], Eq[-2], Eq[-1])
    
    Eq.induct = Eq[2].subs(n, n + 1)
    
    Eq << discrete.continued_fraction.HK.definition.apply(x, n, H, K)

    Eq << Eq.induct.subs(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << -Eq[2]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    prove()
