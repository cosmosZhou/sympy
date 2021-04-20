from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.concrete.limits import limits_dependent


@apply
def apply(*given):
    exists_forall_0, exists_forall_1 = given
    (fn0, *limits_f0), *limits_e0 = axiom.exists_forall(exists_forall_0)
    (fn1, *limits_f1), *limits_e1 = axiom.exists_forall(exists_forall_1)
    
    assert not limits_dependent(limits_e0, limits_e1)
    assert not limits_dependent(limits_f0, limits_f1)
    
    return Exists(ForAll(fn0 & fn1, *limits_f0, *limits_f1), *limits_e0, *limits_e1)


@prove
def prove(Eq):
    N = Symbol.N(integer=True)    
    M = Symbol.M(integer=True)
    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Exists[M](ForAll[x:A](f(x) <= M)), Exists[N](ForAll[y:B](g(y) <= N)))
    
    Eq << Eq[-1].this.function.apply(algebra.forall_et.given.et)
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
if __name__ == '__main__':
    prove()
    
from . import limits_intersect
