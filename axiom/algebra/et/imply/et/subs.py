from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, index=None, reverse=False):
    eqs = axiom.is_And(given)
    
    if index is None:        
        for eq in eqs:
            if eq.is_Equal:
                break
    else:
        eq = eqs[index] 
        
    assert eq.is_Equal
    old, new = eq.args
    if reverse:
        old, new = new, old
            
    conds = []
    for cond in eqs:
        if cond is not eq:
            cond = cond._subs(old, new)
            conds.append(cond)
    
    return And(eq, *conds)            


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    
    Eq << apply(Unequal(x, y) & Unequal(f(x), g(y)) & Equal(f(x), b))
    
    Eq << algebra.et.imply.cond.apply(Eq[0])    
    
    Eq << Eq[-2].subs(Eq[2])
    
    Eq <<= Eq[-1] & Eq[-2] & Eq[2]


if __name__ == '__main__':
    prove()

