from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, index=None):
    fx, fy = axiom.is_Sufficient(given)
    eqs = axiom.is_And(fy)
    
    if isinstance(index, slice):
        eqs = eqs[index]
        return tuple(Sufficient(fx, eq) for eq in eqs)
    
    if index is None:
        return tuple(Sufficient(fx, eq) for eq in eqs)
    
    return Sufficient(fx, eqs[index])


@prove
def prove(Eq):        
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    f = Function.f(integer=True)
    h = Function.h(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Sufficient(Equal(h(x), h(y)), Equal(f(x), f(y)) & Equal(g(x), g(y))), index=0)
    
    Eq << Eq[0].this.rhs.apply(algebra.et.imply.cond, index=0)
    
        
if __name__ == '__main__':
    prove()

