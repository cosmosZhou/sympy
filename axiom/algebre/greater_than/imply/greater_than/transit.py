from axiom.utility import prove, apply
from sympy.core.relational import Unequal, StrictGreaterThan, GreaterThan
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom import algebre


@apply(imply=True)
def apply(given, lower):
    assert given.is_GreaterThan
    lhs, rhs = given.args
    assert rhs >= lower
    return GreaterThan(lhs, lower)




@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    z = Symbol.z(domain=Interval(-oo, y))
    Eq << apply(x >= y, z)
    
    Eq << GreaterThan(y, z, plausible=True)
    
    Eq << algebre.greater_than.greater_than.imply.greater_than.transit.apply(Eq[0], Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)
