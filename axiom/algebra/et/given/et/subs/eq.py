from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(imply, index=None, reverse=False):
    eqs = axiom.is_And(imply)
    
    if index is None:
        for index, eq in enumerate(eqs):
            if eq.is_Equal:
                break
        else:
            return
        
    eq = eqs.pop(index)
        
    imply = And(*eqs)
    
    old, new = axiom.is_Equal(eq) 
    
    if reverse:
        old, new = new, old
        
    return imply._subs(old, new) & eq


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(integer=True)    

    Eq << apply(NotContains(f(x), S) & Equal(x, y))
    
    Eq << algebra.et.imply.cond.apply(Eq[1])
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq <<= Eq[-1] & Eq[-2]
        
if __name__ == '__main__':
    prove()


