from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from axiom import algebre


@apply(imply=True)
def apply(given):
    x = axiom.is_nonnegative(given)
    return Equality(abs(x), x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x >= 0)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << algebre.condition.condition.given.condition.apply(Eq[-1], Eq[0])
        
    
if __name__ == '__main__':
    prove(__file__)
