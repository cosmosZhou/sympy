from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply
def apply(n):
    k = Symbol.k(integer=True)
    return Equality(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True, positive=True)
    Eq.is_continuous = Equality(Limit[x:x0:"+-"](1 / x), 1 / x0, plausible=True)

    Eq << Eq.is_continuous.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Interval(*ab, right_open=True, integer=True))

    Eq << Eq.is_continuous.apply(algebre.cond.imply.forall.restrict, (x0, k, k + 1))

    Eq.mean_value_theorem = axiom.calculus.integral.mean_value_theorem.apply(Eq[-1])

    Eq << algebre.imply.forall.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].inverse()
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.interval)
    
    Eq << algebre.forall_et.imply.forall.apply(Eq[-1])
    
    Eq <<= Eq[-2].subs(Eq.mean_value_theorem.reversed), Eq[-1].subs(Eq.mean_value_theorem.reversed)

    Eq <<= Eq[-1].apply(algebre.ge.imply.ge.sum, (k, 1, n - 1)), Eq[-2].apply(algebre.le.imply.le.sum, (k, 1, n)) 
    
    Eq <<= Eq[-1].this.lhs.doit(), Eq[-2].this.lhs.doit().reversed
    
    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.limits_subs(k, k - 1) + 1

    assert Eq[-3].lhs > 0    
    Eq <<= Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs 
    
    Eq <<= Eq[-2].limit(n, oo), Eq[-1].limit(n, oo)
    
    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    prove(__file__)

