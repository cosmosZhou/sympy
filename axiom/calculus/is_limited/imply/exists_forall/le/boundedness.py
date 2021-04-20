from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, calculus, sets
from axiom.calculus.eq.to.exists_forall.limit_definition import exists_forall


@apply
def apply(given, δ=None, var=None):
    fn, (x, x0, dir) = axiom.is_limited(given)
    
    M = fn.generate_free_symbol(excludes={x}, free_symbol=var, positive=True, real=True)
    exists = exists_forall(Equal(given.lhs, S.Zero), M, δ=δ)
    
    limits = exists.limits + (M,)
    return exists.func(exists.function, *limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
#     x = Symbol.x(integer=True)
    
    f = Function.f(real=True, shape=())
        
    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))
    
#     x0 = oo
#     x0 = -oo
    
    a = Symbol.a(real=True)    
#     a = oo
#     a = -oo

    direction = 1
    
    Eq << apply(Contains(Limit[x:x0:direction](f(x)), Reals), var='M')
    
    M = Eq[-1].variables[1]
    
    Eq << calculus.is_limited.imply.exists_forall.limit_definition.symbol_subs.apply(Eq[0], var='A')
    
    A = -Eq[-1].function.function.lhs.arg.args[0]
    Eq << Eq[-1].this.function.function.apply(algebra.lt.imply.cond.split.abs)
         
    Eq << Eq[-1].this.function.function.args[0] + A
    
    Eq << Eq[-1].this.function.function.args[0] + A
    
    Eq << Eq[-1].this.function.function.apply(algebra.lt.gt.imply.lt.abs.max)
    
    Eq << algebra.cond.imply.exists.subs.apply(Eq[-1], Eq[-1].function.function.rhs, M)
    
    
if __name__ == '__main__':
    prove()
