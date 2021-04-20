from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, *, cond=None):
    lhs, rhs = axiom.is_Sufficient(given)
    return Sufficient(cond | lhs, cond | rhs)


@prove
def prove(Eq):
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
        
    Eq << apply(Sufficient(a > b, f(a) > g(b)), cond=x > y)
    
    Eq << algebra.sufficient.imply.ou.apply(Eq[0])
    
    Eq << algebra.sufficient.given.ou.apply(Eq[1])
    
    Eq << algebra.ou.given.et.apply(Eq[-1])
    
    Eq << algebra.ou.given.ou.apply(Eq[-1], Slice[:2])
    
        
if __name__ == '__main__':
    prove()
