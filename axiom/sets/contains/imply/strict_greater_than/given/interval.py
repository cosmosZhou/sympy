from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, Subset
from sympy import Symbol
import axiom
from sympy.logic.boolalg import Or, And
from axiom import sets
from sympy.sets.sets import Interval
from sympy.core.relational import LessThan, GreaterThan, StrictGreaterThan


@plausible
def apply(given):
    assert given.is_Contains
    x, interval = given.args
    assert interval.is_Interval
    a, b = interval.args
    
    if interval.left_open:
        return StrictGreaterThan(x, a)
    else:
        if interval.right_open:
            return StrictGreaterThan(b, x)
        else:
            ...
        

from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, left_open=True)))
    
    Eq << Eq[0].split()
    
if __name__ == '__main__':
    prove(__file__)

