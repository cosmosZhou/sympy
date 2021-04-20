from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    xy = axiom.is_positive(given)
    x, y = axiom.is_Mul(xy)
    return Or((x < 0) & (y < 0), (x > 0) & (y > 0))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
        
    Eq << apply(x * y > 0)
    
    Eq << ~Eq[-1]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)
    
    Eq << Eq[-1].this.args[0].apply(algebra.is_nonpositive.is_nonnegative.imply.is_nonpositive)

    Eq << Eq[-1].this.args[0].apply(algebra.is_nonnegative.is_nonpositive.imply.is_nonpositive)
    
    Eq << Eq[-1].this.args[0] * y
    
    Eq << Eq[-1].this.args[1] * x
    
    Eq <<= Eq[-1] & Eq[0]
            
if __name__ == '__main__':
    prove()




