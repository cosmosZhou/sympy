from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete
import axiom

from axiom.discrete.imply.is_positive.alpha import alpha
from axiom.discrete.continued_fraction.HK.definition import H, K


@apply
def apply(given):
    xj, *limits = axiom.forall_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 1
    x, _j = axiom.is_Indexed(xj)
    assert _j == j
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq): 
    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    j = Symbol.j(integer=True)
    
    Eq << apply(ForAll[j:1:n](x[j] > 0))
    
    Eq << algebra.cond.given.sufficient.bisected.apply(Eq[1], cond=n >= 3)
    
    Eq.case1, Eq.case2 = algebra.sufficient.given.sufficient.split.apply(Eq[-1], cond=n < 2)
    
    Eq << Eq.case1.this.lhs.apply(algebra.lt.to.eq.squeeze)
    
    Eq << Eq[-1].this.apply(algebra.sufficient.subs)
    
    Eq << Eq[-1].this.find(alpha).definition
    
    Eq << Eq[-1].this.find(H).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq.case2.this.apply(algebra.sufficient.subs)
    
    Eq << Eq[-1].this.find(alpha).definition
    
    Eq << Eq[-1].this.find(alpha).definition
    
    Eq << Eq[-1].this.find(H).definition
    
    Eq << Eq[-1].this.find(K).definition
    
    Eq << Eq[-1].this.rhs.rhs.expand()
    
    n_ = Symbol.n(domain=Interval(3, oo, integer=True))
    Eq << discrete.imply.sufficient.alpha.HK.apply(x[:n_], wrt=j)
    
    Eq << Eq[0].subs(n, n_)
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].forall((n_,))
    
    _n = Eq[-1].variable    
    Eq << algebra.forall.imply.sufficient.apply(Eq[-1])
    
    Eq << Eq[-1].subs(_n, n)
    

        
if __name__ == '__main__':
    prove()

from . import offset0
