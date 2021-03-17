from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    is_nonnegative, less_than = given
    if not less_than.is_LessThan:
        less_than, is_nonnegative = given
    
    x = axiom.is_nonnegative(is_nonnegative)
    _x, M = axiom.is_LessThan(less_than)
    assert x == _x
    
    return LessThan(x * x, M * M)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    M = Symbol.M(real=True)
    
    Eq << apply(x >= 0, x <= M)
    
    Eq << algebre.ge.le.imply.ge.transit.apply(Eq[0], Eq[1])
    
    Eq << -Eq[-1]
    
    Eq << algebre.ge.le.imply.ge.transit.apply(Eq[0], Eq[-1])
    
    Eq << algebre.ge.le.imply.is_nonpositive.apply(Eq[-1], Eq[1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1] - Eq[-1].lhs.args[0]

    
if __name__ == '__main__':
    prove(__file__)
