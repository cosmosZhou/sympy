from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, d=1, evaluate=False):
    d = sympify(d)
    assert d.is_integer and d > 0
    return LessThan(Floor(x / d) * d, x, evaluate=evaluate)

@prove
def prove(Eq):
    x = Symbol.x(real=True)
    d = Symbol.d(integer=True, positive=True)
     
    Eq << apply(x, d)
    
    Eq << Eq[-1] / d

    
if __name__ == '__main__':
    prove(__file__)

