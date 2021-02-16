from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given: |A| >= 1
# A != {}


@apply(imply=True)
def apply(*given):
    greater_than, _greater_than = given
    x, a = axiom.is_LessThan(greater_than)
    b, _x = axiom.is_LessThan(_greater_than)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    assert x == _x

    return Contains(x, Interval(b, a, integer=x.is_integer))




@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    x = Symbol.x(real=True, given=True)
    
#     Eq << apply(x >= b, a >= x)    
    Eq << apply(x <= b, a <= x)
    
    Eq << sets.contains.given.et.apply(Eq[-1]).split()
    
    Eq << Eq[-1].reversed

if __name__ == '__main__':
    prove(__file__)

