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
    
    return Equal(Limit[x:x0:dir](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    dir = S.One
    Eq << apply(Contains(Limit[x:x0:dir](f(x)), Reals), Contains(Limit[x:x0:dir](g(x)), Reals))
    
    is_zero = And(Equal(Eq[0].lhs, 0), Eq[1])
    Eq << Sufficient(is_zero, is_zero, plausible=True)
    
    Eq.is_zero = Eq[-1].this.rhs.apply(calculus.is_zero.is_limited.imply.eq.algebraic_limit_theorem.mul)

    Eq << Eq[-1].this.rhs.args[1].apply(sets.contains.imply.exists_eq, var='B', simplify=None)
    
    Eq << Eq[-1].this.rhs.apply(algebra.cond.exists.imply.exists_et, simplify=None)
    
    Eq << Eq[-1].this.rhs.function.apply(algebra.eq.eq.imply.eq.mul)
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.et.apply(Eq.is_zero, Eq[-1])
    
    Eq.mul_is_zero = Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit, reverse=True)

    is_nonzero = And(Contains(Eq[0].lhs, Reals // {0}), Eq[1])
    Eq << Sufficient(is_nonzero, is_nonzero, plausible=True)
    
    Eq << Eq[-1].this.rhs.apply(calculus.is_limited.is_limited.imply.eq.algebraic_limit_theorem.multiply.nonzero)
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.ou.apply(Eq.mul_is_zero, Eq[-1])
    
    Eq << Eq[-1].this.lhs.args[0].args[0].apply(sets.eq.given.contains)
    
    Eq <<= Eq[0] & Eq[1]
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[-1], Eq[-2])
    
if __name__ == '__main__':
    prove()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

from . import nonzero

