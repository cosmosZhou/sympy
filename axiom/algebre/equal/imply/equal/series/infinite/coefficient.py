from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply(imply=True)
def apply(given, x):
    lhs, rhs = axiom.is_Equal(given)
    an = axiom.is_infinite_series(lhs)
    bn = axiom.is_infinite_series(rhs)
    n = lhs.variable
    an /= x ** n
    bn /= x ** n
    return Equality(an, bn)


@prove
def prove(Eq):
    A = Symbol.A(shape=(oo,), real=True)
    B = Symbol.B(shape=(oo,), real=True)
    x = Symbol.x(real=True)
    n = Symbol.n(integer=True)
    Eq << apply(Equality(Sum[n:0:oo](A[n] * x ** n), Sum[n:0:oo](B[n] * x ** n)), x=x)
    
    Eq << Eq[0].subs(x, 0)
    
    Eq << Eq[-1].this.lhs().function.simplify()
    
    Eq.initial = Eq[-1].this.rhs().function.simplify()

    m = Symbol.m(integer=True, nonnegative=True)
    Eq.hypothesis = Eq[1].subs(n, m)
    
    Eq.induction = Eq.hypothesis.subs(m, m + 1)
    
    k = Symbol.k(domain=Interval(0, m, integer=True))
    
    Eq << Eq.hypothesis.subs(m, k)
    
    Eq << Eq[-1] * x ** k
    
    Eq << algebre.equal.imply.equal.sum.apply(Eq[-1], (k,))
    
    _k = Symbol.k(integer=True)
    Eq << Eq[-1].this.lhs.limits_subs(k, _k)
    
    Eq << Eq[-1].this.rhs.limits_subs(k, _k)
    
    Eq << Eq[0].this.lhs.limits_subs(n, _k)
    
    Eq << Eq[0].this.rhs.limits_subs(n, _k)
    
    Eq << Eq[0] - Eq[-1]
    
    Eq << Eq[-1].this.lhs.astype(Sum)
    
    Eq << Eq[-1].this.rhs.astype(Sum)
    
    r = Symbol.r(real=True, positive=True)
    
    Eq << Eq[-1].subs(x, r)
    
    Eq << Eq[-1].this.lhs.limits_subs(_k, _k + m + 1)
    
    Eq << Eq[-1].this.rhs.limits_subs(_k, _k + m + 1)
    
    Eq << Eq[-1].this.lhs.astype(Times)
    
    Eq << Eq[-1].this.rhs.astype(Times)
    
    Eq << algebre.equal.imply.equal.limit.apply(Eq[-1], r, 0)
    
    Eq << Eq[-1].this.lhs.astype(Sum)
    
    Eq << Eq[-1].this.rhs.astype(Sum)
    
    Eq << Eq[-1].this.lhs.bisect({0})
    
    Eq << Eq[-1].this.rhs.bisect({0})
    
    Eq << Eq[-1].this.lhs.args[1]().function.doit()
    
    Eq << Eq[-1].this.rhs.args[1]().function.doit()

    Eq << Eq.induction.induct()
    
    Eq << algebre.equal.sufficient.imply.equal.second.induction.where.basic.apply(Eq.initial, Eq[-1], n=m + 1, k=k, hypothesis=True)
    
    Eq << Eq.induction.subs(m, m - 1)
    
    Eq << Eq[-1].subs(m, n)

    Eq << algebre.ou.imply.forall.apply(Eq[-1], pivot=1)
    
    Eq <<= Eq[-1] & Eq.initial
    
if __name__ == '__main__':
    prove(__file__)

