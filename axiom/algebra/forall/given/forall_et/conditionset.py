from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
from sympy.concrete.limits import limits_cond


@apply(simplify=False)
def apply(imply):
    fn, *limits = axiom.is_ForAll(imply)
    x, cond, baseset = axiom.limit_is_baseset(limits)    
    return ForAll(fn & cond, *limits)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)    
    g = Function.g(shape=(), integer=True)
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(ForAll[x:g(x) > 0:A](f(x) > 0))  
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[1])    


if __name__ == '__main__':
    prove()

