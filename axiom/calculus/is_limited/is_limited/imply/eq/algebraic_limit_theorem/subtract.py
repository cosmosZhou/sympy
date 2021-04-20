from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets, calculus


@apply
def apply(*given):
    limited_f, limited_g = given
    fx, (x, x0, dir) = axiom.is_limited(limited_f)
    
    gx, (_x, _x0, _dir) = axiom.is_limited(limited_g)
    assert dir == _dir
    
    assert x == _x
    assert x0 == _x0
    
    return Equal(Limit[x:x0:dir](fx - gx), limited_f.lhs - limited_g.lhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(Contains(Limit[x:oo](f(x)), Reals), Contains(Limit[x:oo](g(x)), Reals))
    
    ε = Symbol.ε(real=True, positive=True)
    
    ε0 = Symbol.ε_0(real=True, positive=True)
    N0 = Symbol.N_0(real=True, positive=True)
    
    Eq << calculus.is_limited.imply.exists_forall.limit_definition.symbol_subs.apply(Eq[0], ε0, N0, var='A')    
    Eq << Eq[-1].subs(ε0, ε / 2)
    
    ε1 = Symbol.ε_1(real=True, positive=True)
    N1 = Symbol.N_1(real=True, positive=True)
    
    Eq << calculus.is_limited.imply.exists_forall.limit_definition.symbol_subs.apply(Eq[1], ε1, N1, var='B')
    Eq << Eq[-1].subs(ε1, ε / 2)
    
    Eq << algebra.exists_forall.exists_forall.imply.exists_forall_et.limits_intersect.apply(Eq[-1], Eq[-3])
    
    Eq << Eq[-1].this.function.function.apply(algebra.lt.lt.imply.lt.abs.sub)
    
    Eq << Eq[-1].this.function.limits[0][1].apply(algebra.et.given.gt)

    N = Symbol.N(real=True, positive=True)
    
    Eq << algebra.exists.imply.exists.subs.apply(Eq[-1], Max(N0, N1), N)
    
    Eq << calculus.exists_forall.imply.eq.limit_definition.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[0].args[1].definition
    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

