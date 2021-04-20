from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.concrete.limits import limits_dependent, limits_intersect


@apply
def apply(*given):
    exists_forall_0, exists_forall_1 = given
    (fn0, *limits_f0), *limits_e0 = axiom.exists_forall(exists_forall_0)
    (fn1, *limits_f1), *limits_e1 = axiom.exists_forall(exists_forall_1)
    
    assert not limits_dependent(limits_e0, limits_e1)
    
    assert len(limits_f0) == len(limits_f1)
    assert all(x == y for (x, *_), (y, *_) in zip(limits_f0, limits_f1))
    
    limits_f = limits_intersect(limits_f0, limits_f1)
    return Exists(ForAll(fn0 & fn1, *limits_f), *limits_e0, *limits_e1)


@prove
def prove(Eq):
    N = Symbol.N(integer=True)    
    M = Symbol.M(integer=True)
    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    
    Eq << apply(Exists[M](ForAll[x:A](f(x) <= M)), Exists[N](ForAll[x:B](g(x) <= N)))
    
    Eq << Eq[-1].this.function.apply(algebra.forall_et.given.et)
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq << Eq[-2].this.function.apply(algebra.forall.given.forall.limits.relaxed, domain=A)
    
    Eq << Eq[-1].this.function.apply(algebra.forall.given.forall.limits.relaxed, domain=B)

    
if __name__ == '__main__':
    prove()
