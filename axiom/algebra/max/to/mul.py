from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    args = axiom.is_Max(self)
    
    common_factors = None
     
    for arg in args:
        if not arg.is_Mul:
            return
                         
        if common_factors is None:
            common_factors = {*arg.args}
        else:   
            common_factors &= {*arg.args}
        
    if common_factors:
        factor = Mul(*common_factors)
        if factor > 0:
            args = [arg / factor for arg in args]
            return Equal(self, factor * Max(*args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    r = Symbol.r(real=True, positive=True)
    
    Eq << apply(Max(x * r, y * r))
    
    Eq << Eq[0].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.astype(Mul)
    
    Eq << Eq[-1].this.lhs.args[0].cond / r
    
    
    
if __name__ == '__main__':
    prove()
