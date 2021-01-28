from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol
import axiom
from sympy.concrete.forall import ForAll
from sympy.core.symbol import Dummy
from sympy import Or
from sympy.core.numbers import oo
from axiom import algebre


@apply(imply=True)
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
    
    return ForAll[wrt:(-1) ** wrt > 0](Equality(lhs, rhs))




@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)
    
    Eq << apply(Equality(f[2 * n], g[2 * n]), wrt=n)
    
    m = Symbol.m(integer=True, even=True)
    assert (m / 2).is_integer
    
    Eq << Eq[0].subs(n, m / 2)
    
    Eq << Eq[-1].forall((m,))
    
    return
    Eq << Eq[-1].astype(Or)
    
    Eq << algebre.ou.imply.ou.invert.apply(Eq[-1])
#     Eq << Eq[-1].bisect((-1) ** n < 0)
    
    
if __name__ == '__main__':
    prove(__file__)
