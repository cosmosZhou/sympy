from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(simplify=False)
def apply(given, *, cond=None):
    lhs, rhs = axiom.is_Sufficient(given)
    return Sufficient(cond & lhs, cond & rhs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True, given=True)    
    f = Symbol.f(integer=True, shape=(oo,), given=True)
    g = Symbol.g(integer=True, shape=(oo,), given=True)
    
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    
    Eq << apply(Sufficient(LessEqual(f[0], g[0]), LessEqual(f[n], g[n])), cond=LessEqual(a, b))
    
    Eq << Sufficient(LessEqual(a, b), LessEqual(a, b), plausible=True)
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.et.apply(Eq[-1], Eq[0], simplify=None)

        
if __name__ == '__main__':
    prove()
