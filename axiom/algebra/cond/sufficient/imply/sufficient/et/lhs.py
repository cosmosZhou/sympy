from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given): 
    cond, sufficient = given
    p, q = axiom.is_Sufficient(sufficient)
    return Sufficient(p & cond, q)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)    
    
    Eq << apply(a > b, Sufficient(x > y, f(x) > g(y)))
    
    Eq << algebra.sufficient.given.ou.apply(Eq[-1])
    
    Eq << ~Eq[-1]
    
    Eq << algebra.cond.cond.imply.cond.apply(Eq[0], Eq[-1])
    
    Eq << algebra.sufficient.imply.ou.apply(Eq[1])
    
    Eq << ~Eq[-1]
    

        
if __name__ == '__main__':
    prove()
