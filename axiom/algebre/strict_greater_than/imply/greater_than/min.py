from sympy import *
from axiom.utility import prove, apply
from axiom import algebre


@apply(imply=True)
def apply(given, m):
    assert given.is_StrictGreaterThan
    lhs, rhs = given.args
    return GreaterThan(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    z = Symbol.z(real=True, given=True)
    Eq << apply(x > y, z)
    Eq << algebre.strict_greater_than.imply.greater_than.integer.apply(Eq[0])
    
    Eq << algebre.greater_than.imply.greater_than.min.apply(Eq[-1], z)    

if __name__ == '__main__':
    prove(__file__)
