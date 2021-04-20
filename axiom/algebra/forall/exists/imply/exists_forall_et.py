from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom
from sympy.concrete.limits import limits_dependent


@apply
def apply(*given):
    forall, exists = given
    fx, *limits_f = axiom.is_ForAll(forall) 
    fy, *limits_e = axiom.is_Exists(exists)
    
    assert not limits_dependent(limits_f, limits_e)        
    return Exists(ForAll(fx & fy, *limits_f), *limits_e)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    z = Symbol.z(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)

    Eq << apply(ForAll[z:h(z) > 0](h(y, z) > 0), Exists[y:g(y) > 1, x:f(x) > 0](g(x) > 0))
    
    Eq << Eq[-1].this.function.apply(algebra.forall_et.given.et)

#     Eq << Eq[-1].this.find(ForAll).apply(algebra.forall.given.cond)
        
    Eq << algebra.cond.exists.imply.exists_et.apply(Eq[0], Eq[1])
    

if __name__ == '__main__':
    prove()

