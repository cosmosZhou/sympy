from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets, calculus


@apply
def apply(*given):
    limited_f, limited_g = given
    fx, (x, x0, dir) = axiom.is_limited(limited_f)
    assert dir == 0
    gx, (_x, _x0, dir) = axiom.is_limited(limited_g)
    assert dir == 0
    
    assert x == _x
    assert x0 == _x0
    
    return Equal(Limit[x:x0](fx + gx), limited_f.lhs + limited_g.lhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(Contains(Limit[x:x0](f(x)), Reals), Contains(Limit[x:x0](g(x)), Reals))
    
    ε = Symbol.ε(real=True, positive=True)
    
    ε0 = Symbol.ε_0(real=True, positive=True)
    δ0 = Symbol.δ_0(real=True, positive=True)
    
    Eq << calculus.is_limited.imply.exists_forall.limit_definition.symbol_subs.apply(Eq[0], ε0, δ0, var='A')    
    Eq << Eq[-1].subs(ε0, ε / 2)
    
    ε1 = Symbol.ε_1(real=True, positive=True)
    δ1 = Symbol.δ_1(real=True, positive=True)
    
    Eq << calculus.is_limited.imply.exists_forall.limit_definition.symbol_subs.apply(Eq[1], ε1, δ1, var='B')
    Eq << Eq[-1].subs(ε1, ε / 2)
            
    Eq << algebra.exists_forall.exists_forall.imply.exists_forall_et.limits_intersect.apply(Eq[-1], Eq[-3])
    
    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.abs.add)
    
    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains)
    
    Eq << Eq[-1].this.function.limits[0][1].args[0].apply(sets.lt.given.contains)
    
    Eq << Eq[-1].this.function.limits[0][1].args[1].simplify()
      
    δ = Symbol.δ(real=True, positive=True)
    
    Eq << algebra.exists.imply.exists.subs.apply(Eq[-1], Min(δ0, δ1), δ)

    Eq << calculus.exists_forall.imply.eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

