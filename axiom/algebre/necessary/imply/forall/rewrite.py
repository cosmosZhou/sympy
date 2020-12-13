from axiom.utility import plausible
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll, Necessary, Or
import axiom
from axiom import algebre


@plausible
def apply(given, wrt=None):
    fn1, fn = axiom.is_Necessary(given)        
    if wrt is None:
        wrt = fn.wrt
    return ForAll[wrt:fn](fn1)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Necessary(Equal(f[n + 1], g[n + 1]), Equal(f[n], g[n])), wrt=n)
    
    Eq << Eq[0].astype(Or)
    
    Eq << algebre.ou.imply.forall.apply(Eq[-1], pivot=1, wrt=n)

        
if __name__ == '__main__':
    prove(__file__)
