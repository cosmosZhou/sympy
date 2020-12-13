from axiom.utility import plausible
from sympy.core.relational import LessThan, GreaterThan, StrictLessThan
from sympy import Symbol
import axiom
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom import algebre


@plausible
def apply(given, upper=None):    
    x, a = axiom.is_LessThan(given)
    assert a < upper
    
    return StrictLessThan(x, upper)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True))

    Eq << apply(x <= a, b)
    
    Eq << StrictLessThan(a, b, plausible=True)
    
    Eq << algebre.less_than.strict_less_than.imply.strict_less_than.transit.apply(Eq[0], Eq[-1])    

    
if __name__ == '__main__':
    prove(__file__)
