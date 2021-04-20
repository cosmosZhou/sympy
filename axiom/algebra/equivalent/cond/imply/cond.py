from axiom.utility import prove, apply
from sympy import *

import axiom
from axiom import algebra


@apply
def apply(*given):
    equivalent, condition = given
    fn, fn1 = axiom.is_Equivalent(equivalent)        
    return condition._subs(fn, fn1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    
    Eq << apply(Equivalent(f[n] > 0, g[n] > 0), ForAll[n:f[n] > 0](h[n] > 0))
    
    Eq << algebra.equivalent.imply.eq.apply(Eq[0])
    
    Eq << ForAll[n:Equal(Bool(f[n] > 0), 1)](h[n] > 0, plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].lhs.definition
    
    Eq << Eq[-1].this.limits[0][1].subs(Eq[-2])
    
    Eq << Eq[-1].this.limits[0][1].lhs.definition

        
if __name__ == '__main__':
    prove()
