from sympy import ForAll, LAMBDA, Boole, Or
from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo, Zero

import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import Sufficient


@apply
def apply(given):
    p, q = axiom.is_Sufficient(given)
        
    return Equal(Boole(p), Boole(p) * Boole(q))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Sufficient(Equal(Boole(Eq[0].lhs), 1), Equal(Boole(Eq[0].rhs), 1), plausible=True)
    
    Eq << Eq[-1].this.lhs.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.lhs.astype(Piecewise)
    
    Eq << Eq[-2].astype(Or)
    
    Eq << Eq[-1].this.args[1].apply(algebre.unequal.imply.is_zero.bool)
    
    Eq << algebre.ou.imply.is_zero.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    

if __name__ == '__main__':
    prove(__file__)
