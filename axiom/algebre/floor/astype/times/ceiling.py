from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self):
    x = axiom.is_Floor(self)

    return Equality(self, -ceiling(-x))


@prove
def prove(Eq):    
    x = Symbol.x(real=True)
    Eq << apply(floor(x))
        
    Eq << -Eq[0]
    
    Eq << Eq[-1].this.rhs.apply(algebre.ceiling.astype.times)
    
if __name__ == '__main__':
    prove(__file__)

