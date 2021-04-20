from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x):
    return Greater(Floor(x), x - 1)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)
    
    Eq << Eq[0].reversed + 1 - Floor(x)
    
    Eq << Eq[-1].this.lhs.apply(algebra.add.to.frac)
    
if __name__ == '__main__':
    prove()

