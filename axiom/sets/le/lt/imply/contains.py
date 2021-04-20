from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given: |A| >= 1
# A != {}


@apply
def apply(*given):
    greater_than, strict_greater_than = given
    x, a = axiom.is_LessEqual(greater_than)
    b, _x = axiom.is_Less(strict_greater_than)
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
    Eq << apply(x <= b, a < x)
    
    Eq << sets.contains.given.et.split.interval.apply(Eq[-1])
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove()

