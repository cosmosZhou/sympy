from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x):
    return StrictLessThan(x, Floor(x) + 1)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)
    
    Eq << algebre.imply.gt.floor.apply(x)
    
    Eq << Eq[-1] + 1
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

