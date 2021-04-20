from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given): 
    cond, sufficient = given
    p, q = axiom.is_Sufficient(sufficient)
    return Sufficient(p, q & cond)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)    
    
    Eq << apply(a > b, Sufficient(x > y, f(x) > g(y)))
    
    Eq << algebra.sufficient.given.sufficient.split.et.apply(Eq[-1])
    
    Eq << algebra.sufficient.given.ou.apply(Eq[-1])
    
    Eq << algebra.cond.imply.ou.apply(Eq[0], cond=x <= y)
    
        
if __name__ == '__main__':
    prove()
