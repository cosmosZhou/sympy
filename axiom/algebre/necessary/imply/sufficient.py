from axiom.utility import plausible
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, LAMBDA, Or, Necessary
import axiom
from axiom import algebre


@plausible
def apply(given):
    fn, fn1 = axiom.is_Necessary(given)        
    return Sufficient(fn1, fn)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Necessary(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq << Eq[0].reversed
        
if __name__ == '__main__':
    prove(__file__)
