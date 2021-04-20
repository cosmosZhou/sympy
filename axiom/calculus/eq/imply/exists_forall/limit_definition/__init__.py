from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom.calculus.eq.to.exists_forall.limit_definition import exists_forall
from axiom import algebra, calculus

@apply
def apply(given, ε=None, δ=None):
    return exists_forall(given, ε, δ)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
    x = Symbol.x(integer=True)
    
    f = Function.f(real=True, shape=())
        
    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))
    
    x0 = oo
#     x0 = -oo
    
    a = Symbol.a(real=True)    
#     a = oo
#     a = -oo

    direction = 1
    
    Eq << apply(Equal(Limit[x:x0:direction](f(x)), a))
    
    Eq << calculus.eq.to.exists_forall.limit_definition.apply(Eq[0])
        
    Eq << algebra.cond.equivalent.imply.cond.transit.apply(Eq[0], Eq[-1])
    
    
if __name__ == '__main__':
    prove()

del limit
from . import limit
