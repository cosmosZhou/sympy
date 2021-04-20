from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(*given):
    equality_A, equality_B = given
    x, a = axiom.is_Equal(equality_A)    
    _x, b = axiom.is_Equal(equality_B)
    assert x == _x
    
    return Contains(x, a.set & b.set)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    
    Eq << apply(Equal(x, a), Equal(x, b))
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[1])
    
    Eq << Eq[-2].subs(Eq[-1])
    

if __name__ == '__main__':
    prove()

