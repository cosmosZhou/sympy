from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x):
    return StrictGreaterThan(x, Ceiling(x) - 1)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)
    
    Eq << algebre.imply.strict_less_than.ceiling.apply(x)
    
    Eq << Eq[-1].reversed
    
    Eq << Eq[-1] - 1

    
if __name__ == '__main__':
    prove(__file__)

