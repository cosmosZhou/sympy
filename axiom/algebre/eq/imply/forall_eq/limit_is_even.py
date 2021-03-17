from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given, wrt):
    assert wrt.is_symbol    
    lhs, rhs = axiom.is_Equal(given)
    x = Dummy.x(**wrt.dtype.dict)
    lhs = lhs._subs(2 * wrt, x)    
    assert not lhs._has(wrt)
    rhs = rhs._subs(2 * wrt, x)
    assert not rhs._has(wrt)
    
    lhs = lhs._subs(x, wrt)
    rhs = rhs._subs(x, wrt)
    
    return ForAll[wrt:Equal(wrt % 2, 0)](Equality(lhs, rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)
    
    Eq << apply(Equality(f[2 * n], g[2 * n]), wrt=n)
    
    Eq << Eq[1].limits_subs(n, 2 * n)
    
if __name__ == '__main__':
    prove(__file__)
