from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    fn, fn1 = axiom.is_Equivalent(given)        
    return Equal(Bool(fn), Bool(fn1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq << algebra.equivalent.imply.sufficient.apply(Eq[0])
    
    Eq << algebra.sufficient.imply.eq.bool.apply(Eq[-1])
    
    Eq << algebra.equivalent.imply.necessary.apply(Eq[0])
    
    Eq << algebra.necessary.imply.eq.bool.apply(Eq[-1])
    
    Eq << Eq[-1] - Eq[-3]
    
    Eq << algebra.is_zero.imply.eq.apply(Eq[-1], reverse=True)
    
        
if __name__ == '__main__':
    prove()

from . import subs
from . import sum
