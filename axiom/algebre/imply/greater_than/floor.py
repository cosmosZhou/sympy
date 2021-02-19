from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, d):
    d = sympify(d)
    assert d.is_integer and d > 0
    assert x.is_integer
    return GreaterThan(Floor(x / d) * d, x - d + 1)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    d = Symbol.d(integer=True, positive=True)
     
    Eq << apply(x, d)
    
    Eq << algebre.imply.strict_greater_than.floor.apply(x / d)
    
    Eq << Eq[-1] * d
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << algebre.strict_greater_than.imply.greater_than.integer.apply(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)

