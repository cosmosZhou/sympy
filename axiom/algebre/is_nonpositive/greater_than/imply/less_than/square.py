from axiom.utility import plausible
from sympy.core.relational import LessThan, GreaterThan
from sympy import Symbol
import axiom
from axiom import algebre

@plausible
def apply(*given):
    is_nonpositive, greater_than = given
    x = axiom.is_nonpositive(is_nonpositive)
    _x, m = axiom.is_GreaterThan(greater_than)
    assert x == _x
    
    return LessThan(x * x, m * m)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    
    Eq << apply(x <= 0, x >= m)
    
    Eq << algebre.less_than.greater_than.imply.less_than.transit.apply(Eq[0], Eq[1])
    
    Eq << -Eq[-1]

    Eq << algebre.less_than.greater_than.imply.less_than.transit.apply(Eq[0], Eq[-1])
    
    Eq << algebre.greater_than.less_than.imply.is_nonpositive.apply(Eq[1], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1] - Eq[-1].lhs.args[0]
    
if __name__ == '__main__':
    prove(__file__)
