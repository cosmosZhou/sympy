from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
from axiom.algebra.eq.eq.imply.eq.transit import transit


@apply
def apply(imply, swap=False, reverse=False):
    ab, bc = axiom.is_And(imply)
    if swap:
        ab, bc = bc, ab        
    ac = transit(ab, bc, reverse=reverse)
    return ab, ac


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True, shape=(oo,))
    b = Symbol.b(integer=True, shape=(oo,))
    c = Symbol.c(integer=True, shape=(oo,))
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Equal(a[i], b[i]) & Equal(b[i], c[i]))
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[1], Eq[2])
    
    Eq <<= Eq[-1] & Eq[1]
    
    
if __name__ == '__main__':
    prove()

