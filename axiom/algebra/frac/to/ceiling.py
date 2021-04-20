from sympy import *
from axiom.utility import prove, apply
import axiom

@apply
def apply(fraction):
    x = axiom.is_FractionalPart(fraction)
     
    return Equal(fraction, x + ceiling(-x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(frac(x))
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].this.rhs.args[1].definition
    
if __name__ == '__main__':
    prove()