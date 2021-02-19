from sympy import Symbol, Min
from axiom.utility import prove, apply
from sympy.core.relational import LessThan

from axiom import algebre


@apply
def apply(given, m):
    assert given.is_LessThan
    lhs, rhs = given.args
    return LessThan(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    z = Symbol.z(real=True, given=True)
    Eq << apply(x <= y, z)
    
    Eq << Eq[0].reversed
    
    Eq << algebre.greater_than.imply.greater_than.min.apply(Eq[-1], z)
    
    Eq << Eq[-1].reversed

if __name__ == '__main__':
    prove(__file__)
