from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol
import axiom
from axiom import algebre, sets


@apply
def apply(given):
    x = axiom.is_negative(given)
    return Equality(abs(x), -x)

@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x < 0)
    
    Eq << -Eq[0]
    
    Eq << algebre.is_positive.imply.equal.abs.apply(Eq[-1])
        
    
if __name__ == '__main__':
    prove(__file__)
