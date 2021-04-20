from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    x = axiom.is_nonnegative(given)
    return Equal(Min(x, 0), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x >= 0)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << algebra.cond.given.et.restrict.apply(Eq[-1], cond=Eq[0])
    
    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1], reverse=True)
        
    
if __name__ == '__main__':
    prove()
