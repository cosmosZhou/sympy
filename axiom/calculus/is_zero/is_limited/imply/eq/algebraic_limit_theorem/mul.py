from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets, calculus


@apply
def apply(*given):
    limited_f, limited_g = given
    limited_f = axiom.is_zero(limited_f)
    fx, (x, x0, dir) = axiom.is_Limit(limited_f)
    
    gx, (_x, _x0, _dir) = axiom.is_limited(limited_g)
    assert dir == _dir
    
    assert x == _x
    assert x0 == _x0
    
    return Equal(Limit[x:x0:dir](fx * gx), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    dir = S.One
    Eq << apply(Equal(Limit[x:x0:dir](f(x)), 0), Contains(Limit[x:x0:dir](g(x)), Reals))
    
    ε = Symbol.ε(real=True, positive=True)
    
    δ0 = Symbol.δ_0(real=True, positive=True)
    
    Eq << calculus.eq.imply.exists_forall.limit_definition.apply(Eq[0], ε, δ0)

    δ1 = Symbol.δ_1(real=True, positive=True)
    
    Eq << calculus.is_limited.imply.exists_forall.le.boundedness.apply(Eq[1], δ=δ1, var='B')
    
    B = Eq[-1].variables[1]
    
    assert B > 0
    Eq << Eq[-2].subs(ε, ε / B)
        
    Eq << algebra.exists_forall.exists_forall.imply.exists_forall_et.limits_intersect.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.abs.mul)
    
    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains)
    
    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains)
    
    Eq << Eq[-1].this.function.limits[0][1].args[1].simplify()
      
    δ = Symbol.δ(real=True, positive=True)
    
    Eq << algebra.exists.imply.exists.subs.apply(Eq[-1], Min(δ0, δ1), δ)
    
    Eq << calculus.exists_forall.imply.eq.limit_definition.apply(Eq[-1])

    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

