from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x):
    return StrictLessThan(Ceiling(x), x + 1)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)
    
    Eq << Eq[-1].this.lhs.apply(algebre.ceiling.astype.times)
    
    Eq << Eq[-1] - x
    
    Eq << Eq[-1].this.lhs.apply(algebre.plus.astype.frac)

    
if __name__ == '__main__':
    prove(__file__)

