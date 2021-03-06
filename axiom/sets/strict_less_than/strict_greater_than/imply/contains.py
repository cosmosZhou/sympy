from sympy.core.relational import GreaterThan
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import Exists
from sympy.sets.contains import Contains
from axiom import algebre, sets
import axiom
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
# given: |A| >= 1
# A != {}


@apply(imply=True)
def apply(*given):
    greater_than, _greater_than = given
    x, a = axiom.is_StrictLessThan(greater_than)
    _x, b = axiom.is_StrictGreaterThan(_greater_than)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
        
    assert x == _x

    return Contains(x, Interval(b, a, left_open=True, right_open=True, integer=x.is_integer))


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    x = Symbol.x(real=True, given=True)
    
#     Eq << apply(b < x, a >= x)    
    Eq << apply(x < b, x > a)
    
    Eq << Eq[-1].split()
    
#     Eq << Eq[-1].reversed
    
    Eq << Eq[-2].reversed


if __name__ == '__main__':
    prove(__file__)

