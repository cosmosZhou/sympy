from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given):
    x, max_ab = axiom.is_Less(given)
    ab = axiom.is_Min(max_ab)    
    return tuple(x < a for a in ab)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    
    Eq << apply(x < Min(a, b))  
    
    Eq << algebra.lt.lt.imply.lt.min.apply(Eq[1], Eq[2])
    
if __name__ == '__main__':
    prove()
