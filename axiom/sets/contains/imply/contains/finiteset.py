from sympy import *
from axiom.utility import prove, apply
from axiom import sets
import axiom


@apply
def apply(given, t):
    assert given.is_Contains    
    
    e, finiteset = given.args
    
    args = axiom.is_FiniteSet(finiteset, size=None)    
    
    finiteset = finiteset.func(*(arg + t for arg in args))
        
    return Contains(e + t, finiteset)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    t = Symbol.t(real=True)
    
    Eq << apply(Contains(x, {a, b}), t)
    
    Eq << sets.contains.imply.ou.having.finiteset.two.apply(Eq[0], simplify=None)
    
    Eq << Eq[-1].this.args[0] + t
    
    Eq << Eq[-1].this.args[1] + t
    
    Eq << sets.ou.imply.contains.finiteset.apply(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

