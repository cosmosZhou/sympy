from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, Or
import axiom
from axiom import algebre


@apply
def apply(given, wrt=None):
    fn, fn1 = axiom.is_Sufficient(given)        
    if wrt is None:
        wrt = fn.wrt
    return ForAll[wrt:fn](fn1)




@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])), wrt=n)
    
    Eq << Eq[0].astype(Or)
    
    Eq << algebre.ou.imply.forall.apply(Eq[-1], pivot=1, wrt=n)

        
if __name__ == '__main__':
    prove(__file__)
