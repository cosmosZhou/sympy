from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(imply):
    function, *limits = axiom.is_Exists(imply)
    
    variables = tuple(v for v, *_ in limits)
    return Exists[variables]((function & imply.limits_cond).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)
    Eq << apply(Exists[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))
    
    Eq << algebra.exists_et.imply.exists.limits_absorb.apply(Eq[-1], index=0)
    
    Eq << algebra.exists_et.imply.exists.limits_absorb.apply(Eq[-1], index=0)

    
if __name__ == '__main__':
    prove()
