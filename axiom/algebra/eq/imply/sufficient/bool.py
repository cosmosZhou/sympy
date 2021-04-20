from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    p, q = axiom.is_Equal(given)
    if not p.is_Bool:
        p, q = q, p
            
    p = axiom.is_Bool(p)
    _p, q = axiom.is_Mul(q)
    _p = axiom.is_Bool(_p)
    q = axiom.is_Bool(q)
    if p != _p:
        _p, q = q, _p 
    assert p == _p
        
    return Sufficient(p, q)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equal(Bool(Equal(f[n], g[n])), Bool(Equal(f[n], g[n])) * Bool(Equal(f[n + 1], g[n + 1]))))
    
    Eq << Eq[0] - Eq[0].rhs
    
    Eq << Eq[-1].this.lhs.collect(Eq[0].lhs)
    
    Eq << algebra.is_zero.imply.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].apply(algebra.is_zero.imply.ne, One())
    
    Eq << algebra.ou.imply.sufficient.apply(Eq[-1], pivot=1)
    
    Eq << Eq[-1].this.lhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.definition
    

if __name__ == '__main__':
    prove()
