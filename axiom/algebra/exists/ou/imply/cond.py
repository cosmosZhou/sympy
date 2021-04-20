from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(*given):
    exists, ou = given
    if not exists.is_Exists:
        exists, ou = ou, exists
            
    fx, *limits_x = axiom.is_Exists(exists)
    cond = fx.invert()
    eqs = axiom.is_Or(ou)
    for i, eq in enumerate(eqs):
        if eq == cond:
            del eqs[i]
            return Or(*eqs) 


@prove
def prove(Eq): 
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)    
    A = Symbol.A(etype=dtype.real)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[x:A](f(x, y) > 0), (g(y, x) > 0) | (f(x, y) <= 0))
    
    Eq <<= Eq[0] & Eq[1]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].this.args[0].apply(algebra.cond.exists.imply.exists_et)
    
    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)
    

if __name__ == '__main__':
    prove()

