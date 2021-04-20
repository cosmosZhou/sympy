from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given):
    p, q = axiom.is_Sufficient(given)
        
    return Equal(Bool(p), Bool(p) * Bool(q))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Sufficient(Equal(Bool(Eq[0].lhs), 1), Equal(Bool(Eq[0].rhs), 1), plausible=True)
    
    Eq << Eq[-1].this.lhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-2].apply(algebra.sufficient.imply.ou)
    
    Eq << Eq[-1].this.args[1].apply(algebra.ne.imply.is_zero.bool)
    
    Eq << algebra.ou.imply.is_zero.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    

if __name__ == '__main__':
    prove()
