from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply(simplify=False)
def apply(given):
    y, s = axiom.is_Contains(given)
    
    x, expr, base_set = axiom.is_ImageSet(s)
    
    return Exists[x:base_set](Equal(y, expr))


@prove
def prove(Eq):
    y = Symbol.y(integer=True, given=True)
    x = Symbol.x(integer=True)
    f = Function.f(integer=True)
    
    S = Symbol.S(etype=dtype.integer, given=True)

    Eq << apply(Contains(y, imageset(x, f(x), S)))
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].this.function.apply(sets.ne.imply.notcontains)
    
    Eq << sets.forall_notcontains.imply.notcontains.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
    
if __name__ == '__main__':
    prove()

