from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply(imply=True)
def apply(n):
    k = Symbol.k(integer=True)
    return Equality(Limit(Sum[k:1:n](1 / k) / log(n + 1), n, oo), 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True, positive=True)
    Eq.continuity = Equality(Limit(1 / x, x, x0, "+-"), 1 / x0, plausible=True)

    Eq << Eq.continuity.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Interval(*ab, right_open=True, integer=True))

    Eq << Eq.continuity.apply(algebre.condition.imply.forall.minify, (x0, k, k + 1))

    Eq.mean_value_theorem = axiom.calculus.integral.mean_value_theorem.apply(Eq[-1])

    Eq << algebre.imply.forall.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].inverse()
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.interval).split()
    
    Eq <<= Eq[-2].subs(Eq.mean_value_theorem.reversed), Eq[-1].subs(Eq.mean_value_theorem.reversed)

    Eq <<= Eq[-1].apply(algebre.greater_than.imply.greater_than.sum, (k, 1, n - 1)), Eq[-2].apply(algebre.less_than.imply.less_than.sum, (k, 1, n)) 
    
    Eq <<= Eq[-1].this.lhs.doit(), Eq[-2].this.lhs.doit().reversed
    
    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.limits_subs(k, k - 1) + 1

    assert Eq[-3].lhs > 0    
    Eq <<= Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs 
    
    Eq <<= Eq[-2].limit(n, oo), Eq[-1].limit(n, oo)
    
    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    prove(__file__)

