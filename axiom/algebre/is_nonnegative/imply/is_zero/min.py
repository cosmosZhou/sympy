from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, Min
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from axiom import algebre


@apply
def apply(given):
    x = axiom.is_nonnegative(given)
    return Equality(Min(x, 0), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x >= 0)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << algebre.condition.condition.given.condition.apply(Eq[-1], Eq[0], reverse=True)
        
    
if __name__ == '__main__':
    prove(__file__)
