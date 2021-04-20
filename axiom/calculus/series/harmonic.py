from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra, calculus


@apply
def apply(n):
    k = Symbol.k(integer=True)
    return Equal(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True, positive=True)
    Eq.is_continuous = Equal(Limit[x:x0](1 / x), 1 / x0, plausible=True)

    Eq << Eq.is_continuous.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Interval(*ab, right_open=True, integer=True))

    Eq << Eq.is_continuous.apply(algebra.cond.imply.forall.restrict, (x0, k, k + 1))

    Eq.mean_value_theorem = axiom.calculus.integral.mean_value_theorem.apply(Eq[-1])

    Eq << algebra.imply.forall.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].inverse()
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.split.interval)
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1])
    
    Eq <<= algebra.forall.exists.imply.exists_et.apply(Eq[-2], Eq.mean_value_theorem), \
    algebra.forall.exists.imply.exists_et.apply(Eq[-1], Eq.mean_value_theorem)
    
    Eq <<= Eq[-2].this.function.apply(algebra.eq.cond.imply.cond.subs, reverse=True), \
    Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs, reverse=True)
    
    Eq <<= Eq[-2].apply(algebra.cond.imply.forall.restrict, (k, 1, n)), Eq[-1].apply(algebra.cond.imply.forall.restrict, (k, 1, n - 1)) 
    
    Eq <<= algebra.forall_le.imply.le.sum.apply(Eq[-2]), algebra.forall_ge.imply.ge.sum.apply(Eq[-1]) 
    
    Eq <<= Eq[-2].this.lhs.doit(), Eq[-1].this.lhs.doit().reversed
    
    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.limits_subs(k, k - 1) + 1
    
    Eq <<= Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs
    
    Eq <<= calculus.le.imply.le.limit.apply(Eq[-2], (n, oo)), calculus.le.imply.le.limit.apply(Eq[-1], (n, oo))
    
    Eq << Eq[-1].this.rhs.doit()
    
    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    prove()

