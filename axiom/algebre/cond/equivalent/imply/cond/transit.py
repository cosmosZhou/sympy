from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    cond, equivalent = given

    lhs, rhs = axiom.is_Equivalent(equivalent)
    assert cond == lhs
    
    return rhs


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(LessThan(f[0], g[0]), Equivalent(LessThan(f[0], g[0]), LessThan(f[n], g[n])))

    Eq << algebre.equivalent.imply.sufficient.apply(Eq[1])

    Eq << algebre.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
        
if __name__ == '__main__':
    prove(__file__)
