from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets, algebre


@apply
def apply(given):        
    e, S = axiom.is_NotContains(given)
    args = axiom.is_FiniteSet(S, size=None)
    
    eqs = [Unequal(e, s) for s in args]
    
    return And(*eqs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    Eq << apply(NotContains(x, {a, b}))
    
    Eq << algebre.et.given.cond.apply(Eq[1])
    
    Eq << sets.notcontains.imply.ne.apply(Eq[0])
    
    Eq << sets.notcontains.imply.ne.apply(Eq[0], index=1)

    
if __name__ == '__main__':
    prove(__file__)

