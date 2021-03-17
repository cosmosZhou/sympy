from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given: |A| >= 1
# A != {}


@apply
def apply(*given):
    greater_than, strict_greater_than = given
    x, a = axiom.is_LessThan(greater_than)
    _x, b = axiom.is_StrictGreaterThan(strict_greater_than)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
        left_open = False
        right_open = True        
    else:
        left_open = True
        right_open = False
        
    assert x == _x

    return Contains(x, Interval(b, a, left_open=left_open, right_open=right_open, integer=x.is_integer))


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    x = Symbol.x(real=True, given=True)
    
#     Eq << apply(x >= b, a > x)    
    Eq << apply(x <= b, x > a)
    
    Eq << sets.contains.given.et.having.interval.apply(Eq[-1])
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
#     Eq << Eq[-2].reversed


if __name__ == '__main__':
    prove(__file__)

