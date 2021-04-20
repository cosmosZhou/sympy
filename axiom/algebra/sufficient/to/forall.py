from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(given, wrt=None):
    fn, fn1 = axiom.is_Sufficient(given)        
    if wrt is None:
        wrt = fn.wrt
    assert wrt.is_given is None
    return Equivalent(given, ForAll[wrt:fn](fn1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)    
    
    A = Symbol.A(etype=dtype.integer)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Contains(n, A), Equal(f[n], g[n])), wrt=n)
    
    Eq.sufficient, Eq.necessary = algebra.equivalent.given.cond.apply(Eq[0])
    
    Eq << Eq.sufficient.this.lhs.apply(algebra.sufficient.imply.ou)
    
    Eq << Eq[-1].this.lhs.apply(algebra.ou.imply.forall, pivot=1, wrt=n)
    
    Eq << Eq.necessary.this.lhs.apply(algebra.sufficient.given.ou)
    
    Eq << Eq[-1].this.rhs.apply(algebra.forall.imply.ou)

        
if __name__ == '__main__':
    prove()
