from axiom.utility import prove, apply
from sympy.core.relational import Unequal, StrictGreaterThan
from sympy import Symbol


@apply
def apply(given, lower_bound):
    assert given.is_GreaterThan
    lhs, rhs = given.args
    assert rhs > lower_bound
    return StrictGreaterThan(lhs, lower_bound)




@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x >= y, y - 1)
    
    Eq << StrictGreaterThan(y, y - 1, plausible=True)
    
    Eq << Eq[0] + Eq[2]
    
    Eq << Eq[-1] - y
    

if __name__ == '__main__':
    prove(__file__)
