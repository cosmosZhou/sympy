from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol
import axiom
from axiom import algebre


@apply(imply=True)
def apply(given):
    x = axiom.is_positive(given)
    return Equality(abs(x), x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x > 0)
    
    Eq << algebre.strict_greater_than.imply.greater_than.rewrite.apply(Eq[0])
    
    Eq << algebre.is_nonnegative.imply.equal.abs.apply(Eq[-1])
        
    
if __name__ == '__main__':
    prove(__file__)
