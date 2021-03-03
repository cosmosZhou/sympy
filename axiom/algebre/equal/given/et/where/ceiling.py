from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given):
    y, floor_x = axiom.is_Equal(given)
    assert y.is_integer
    x = axiom.is_Ceiling(floor_x)
    return And(x + 1 > y, y >= x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(integer=True)

    Eq << apply(Equal(y, ceiling(x)))
    
    Eq << Eq[-1].split()
    
    Eq <<= -Eq[-2], -Eq[-1]    
    
    Eq << algebre.strict_less_than.less_than.imply.equal.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebre.floor.astype.times.ceiling)
    
    
if __name__ == '__main__':
    prove(__file__)
