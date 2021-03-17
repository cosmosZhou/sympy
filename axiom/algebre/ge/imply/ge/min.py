from sympy import Symbol, Min
from axiom.utility import prove, apply
from sympy.core.relational import GreaterThan

from axiom import algebre


@apply
def apply(given, m):
    assert given.is_GreaterThan
    lhs, rhs = given.args
    return GreaterThan(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    z = Symbol.z(real=True, given=True)
    Eq << apply(x >= y, z)
    
    Eq << Eq[-1] - y
    
    Eq << Eq[-1].this.lhs.astype(Min)
    
    Eq << Eq[-1].this.rhs.astype(Min)
    
    Eq << Eq[0] - y
    
    Eq << algebre.is_nonnegative.imply.is_zero.min.apply(Eq[-1])

    Eq << algebre.eq.imply.eq.min.apply(Eq[-1], -y + z)
    
    Eq << GreaterThan(Min(x - y, -y + z), Min(x - y, 0, -y + z), plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])
    

if __name__ == '__main__':
    prove(__file__)
