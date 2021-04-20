from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import H, K
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(x): 
    assert x.is_positive
    assert x.shape[0].is_finite    
    return Equal(alpha(x), H(x) / K(x))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(integer=True)
    
    Eq.hypothesis = apply(x[:n + 1])
    
    Eq.n2 = Sufficient(n >= 2, Eq.hypothesis, plausible=True)
    
    Eq << Eq.n2.this.apply(algebra.sufficient.to.forall)
    
    _n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    Eq << discrete.continued_fraction.alpha.HK.induction.apply(x, _n)
    
    Eq << Eq[-1].forall((_n,))
    
    Eq.n1 = Sufficient(Equal(n, 1), Eq.hypothesis, plausible=True)
    
    Eq << Eq.n1.this.apply(algebra.sufficient.subs)
    
    Eq << Eq[-1].this.rhs.subs(alpha(x[:2]).this.definition,
                               alpha(x[1]).this.definition,
                               H(x[:2]).this.definition,
                               K(x[:2]).this.definition)
    
    Eq << Eq[-1].this.rhs.rhs.apart(x=x[1])
    
    Eq.n1 = algebra.sufficient.sufficient.imply.sufficient.ou.apply(Eq.n1, Eq.n2)
    
    Eq.n0 = Sufficient(Equal(n, 0), Eq.hypothesis, plausible=True)
    
    Eq << Eq.n0.this.apply(algebra.sufficient.subs)
    
    Eq << Eq[-1].this.rhs.subs(alpha(x[0]).this.definition,
                               H(x[0]).this.definition,
                               K(x[0]).this.definition)
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.ou.apply(Eq.n1, Eq.n0)
        
    Eq << Eq[-1].this.apply(algebra.sufficient.to.forall, wrt=n)
    
    Eq << Eq[-1].simplify()
    
    
if __name__ == '__main__':
    prove()

