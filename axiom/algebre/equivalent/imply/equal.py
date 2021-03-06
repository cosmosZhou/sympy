from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, Boole, Equivalent, Necessary, Or
import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise


@apply(imply=True)
def apply(given):
    fn, fn1 = axiom.is_Equivalent(given)        
    return Equal(Boole(fn), Boole(fn1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq << algebre.equivalent.imply.sufficient.apply(Eq[0])
    
    Eq << algebre.sufficient.imply.equal.bool.apply(Eq[-1])
    
    Eq << algebre.equivalent.imply.necessary.apply(Eq[0])
    
    Eq << algebre.necessary.imply.equal.bool.apply(Eq[-1])
    
    Eq << Eq[-1] - Eq[-3]
    
        
if __name__ == '__main__':
    prove(__file__)
