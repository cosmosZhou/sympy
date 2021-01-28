from sympy import ForAll, LAMBDA, Boole, Or
from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol

from sympy.core.numbers import oo, Zero, One

import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import Sufficient


@apply(imply=True)
def apply(given):
    p, q = axiom.is_Equal(given)
    p = axiom.is_Boole(p)
    _p, q = axiom.is_Times(q)
    _p = axiom.is_Boole(_p)
    q = axiom.is_Boole(q)
    if p != _p:
        _p, q = q, _p 
    assert p == _p
        
    return Sufficient(p, q)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equal(Boole(Equal(f[n], g[n])), Boole(Equal(f[n], g[n])) * Boole(Equal(f[n + 1], g[n + 1]))))
    
    Eq << Eq[0] - Eq[0].rhs
    
    Eq << Eq[-1].this.lhs.collect(Eq[0].lhs)
    
    Eq << algebre.is_zero.imply.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].apply(algebre.is_zero.imply.unequal, One())
    
    Eq << algebre.ou.imply.sufficient.apply(Eq[-1], pivot=1)
    
    Eq << Eq[-1].this.lhs.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.lhs.astype(Piecewise)
    
    

if __name__ == '__main__':
    prove(__file__)
