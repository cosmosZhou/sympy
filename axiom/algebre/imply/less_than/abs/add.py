from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, y):
    assert not x.shape and not y.shape
    return LessThan(abs(x + y), abs(x) + abs(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
     
    Eq << apply(x, y)
    
    Eq << (Eq[0].lhs ** 2).this.expand()
    
    Eq << (Eq[0].rhs ** 2).this.expand()
    
    Eq << algebre.imply.less_than.abs.single.apply(x * y)
    
    Eq << Eq[-1].this.rhs.astype(Times)
    
    Eq << Eq[-1] * 2
    
    Eq << Eq[1] - Eq[2] + Eq[-1]
    
    Eq << Eq[-1] - Eq[-1].lhs.args[1]
    
    Eq << algebre.less_than.imply.less_than.sqrt.apply(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

