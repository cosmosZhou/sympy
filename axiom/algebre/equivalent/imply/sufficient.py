from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, LAMBDA, Equivalent, Necessary
import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise


@apply
def apply(given):
    fn, fn1 = axiom.is_Equivalent(given)        
    return Sufficient(fn, fn1)




@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq << Necessary(*Eq[1].args, plausible=True)
    
    Eq <<= Eq[-1] & Eq[-2]

        
if __name__ == '__main__':
    prove(__file__)
