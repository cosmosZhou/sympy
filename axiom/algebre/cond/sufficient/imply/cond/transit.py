from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    cond, sufficient = given

    lhs, rhs = axiom.is_Sufficient(sufficient)
    assert cond == lhs
    
    return rhs


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True, given=True)    
    f = Symbol.f(integer=True, shape=(oo,), given=True)
    g = Symbol.g(integer=True, shape=(oo,), given=True)
    
    Eq << apply(LessThan(f[0], g[0]), Sufficient(LessThan(f[0], g[0]), LessThan(f[n], g[n])))

    Eq << Eq[1].astype(Or)
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << ~Eq[2]
    
    Eq <<= Eq[-1] & Eq[-2]

        
if __name__ == '__main__':
    prove(__file__)
