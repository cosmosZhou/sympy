from sympy import ForAll, LAMBDA, Boole, Or, Necessary
from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo, Zero

import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import Sufficient


@apply(imply=True)
def apply(given):
    q, p = axiom.is_Necessary(given)
        
    return Equal(Boole(p), Boole(p) * Boole(q))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Necessary(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Eq[0].reversed
    
    Eq << algebre.sufficient.imply.equal.bool.apply(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)
