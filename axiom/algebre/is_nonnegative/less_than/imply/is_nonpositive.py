from axiom.utility import plausible
from sympy.core.relational import LessThan
from sympy import Symbol
import axiom


@plausible
def apply(*given):
    is_nonnegative, less_than = given
    x = axiom.is_nonnegative(is_nonnegative)
    _x, a = axiom.is_LessThan(less_than)
    assert x == _x
    return LessThan(x * (x - a), 0)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, nonnegative=True)

    Eq << apply(x >= 0, x <= a)   
    
    Eq << Eq[1].reversed - x
    
    Eq << Eq[-1] * Eq[0]
    
    Eq << -Eq[-1]
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[2].this.lhs.expand()
    
    
if __name__ == '__main__':
    prove(__file__)
