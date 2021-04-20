from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, calculus, sets
from axiom.calculus.eq.to.exists_forall.limit_definition import exists_forall


@apply
def apply(given, ε=None, δ=None, var=None):
    fn, (x, x0, dir), *R = axiom.is_limited(given)
#     A = given.generate_free_symbol(definition=given)
    
    A = fn.generate_free_symbol(excludes={x}, **fn.type.dict)
    
    cond = exists_forall(Equal(given.lhs, A), ε, δ)
    B = fn.generate_free_symbol(excludes={x}, definition=given.lhs, free_symbol=var)
    return cond._subs(A, B)


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
    
    Eq << apply(Contains(Limit[x:x0:direction](f(x)), Reals), var='A')
    
    Eq << calculus.is_limited.imply.exists_forall.limit_definition.apply(Eq[1])
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
    
if __name__ == '__main__':
    prove()
