from axiom.utility import prove, apply
from sympy.core.relational import LessThan, GreaterThan
from sympy import Symbol
import axiom
from axiom import algebre

@apply
def apply(*given):
    is_nonpositive, greater_than = given
    x = axiom.is_nonpositive(is_nonpositive)
    _x, m = axiom.is_GreaterThan(greater_than)
    assert x == _x
    
    return LessThan(x * x, m * m)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    
    Eq << apply(x <= 0, x >= m)
    
    Eq << algebre.le.ge.imply.le.transit.apply(Eq[0], Eq[1])
    
    Eq << -Eq[-1]

    Eq << algebre.le.ge.imply.le.transit.apply(Eq[0], Eq[-1])
    
    Eq << algebre.ge.le.imply.is_nonpositive.apply(Eq[1], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1] - Eq[-1].lhs.args[0]
    
if __name__ == '__main__':
    prove(__file__)
