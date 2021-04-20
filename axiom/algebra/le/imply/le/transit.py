from axiom.utility import prove, apply
from sympy.core.relational import LessEqual, GreaterEqual
from sympy import Symbol
import axiom
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom import algebra


@apply
def apply(given, upper=None):    
    x, a = axiom.is_LessEqual(given)
    assert a <= upper
    
    return LessEqual(x, upper)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(domain=Interval(a, oo))

    Eq << apply(x <= a, b)
    
    Eq << LessEqual(a, b, plausible=True)
    
    Eq << algebra.le.le.imply.le.transit.apply(Eq[0], Eq[-1])    

    
if __name__ == '__main__':
    prove()
