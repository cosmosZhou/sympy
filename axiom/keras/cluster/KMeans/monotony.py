from sympy import *
from axiom.utility import prove, apply
from axiom import keras, algebra, sets
import axiom
from axiom.keras.cluster.KMeans.nonoverlapping import cluster, mean


@apply
def apply(*given, x=None):
    eq_sum, eq_union = given
    w_sum, M = axiom.is_Equal(eq_sum)
    w_union, M_interval = axiom.is_Equal(eq_union)
    
    zero, _M = axiom.is_Interval(M_interval, integer=True)
    assert _M == M
    assert zero == 0
    
    wi_abs, *limits = axiom.is_Sum(w_sum)
    wi, *_limits = axiom.is_UNION(w_union)
    
    assert limits == _limits
    
    _wi = axiom.is_Abs(wi_abs)
    assert _wi == wi
    
    i = axiom.limit_is_symbol(limits)
    w, _i = axiom.is_Indexed(wi)
    assert _i == i
    
    _M = x.shape[0]
    assert _M == M
    
    w_ = Symbol("omega^'", cluster(w, x))
        
    j = Symbol.j(integer=True)
        
    return LessEqual(Sum[j:w_[i], i](Norm(x[j] - mean(w_[i], x)) ** 2),
                     Sum[j:w[i], i](Norm(x[j] - mean(w[i], x)) ** 2))


@prove
def prove(Eq):
    M = Symbol.M(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    k = Symbol.k(domain=Interval(0, M - 1, integer=True))
        
    x = Symbol.x(real=True, shape=(M, n))
    w = Symbol.omega(shape=(k,), etype=dtype.integer, emptyset=False)
    
    Eq << apply(Equal(Sum[i](abs(w[i])), M), Equal(UNION[i](w[i]), k.domain), x=x)
    
    Eq << keras.cluster.KMeans.equivalent.apply(Eq[1], Eq[2], x=x)
    
    Eq << algebra.equivalent.imply.eq.sum.collapse.apply(Eq[-1], Eq[3].rhs.function)
    
    i_ = Symbol.i(Eq[-1].find(Indexed, Sum))
    
    Eq << Eq[-1].subs(i_.this.definition.reversed)
    
    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.domain_defined.delete)
    
    Eq.plausible = Eq[3].subs(Eq[-1])
    
    Eq << keras.cluster.KMeans.equivalent.w_quote.apply(Eq[1], Eq[2], x=x)
    
    Eq << algebra.equivalent.imply.eq.sum.collapse.apply(Eq[-1], Eq.plausible.lhs.function)
    
    i__ = Symbol("i'", Eq[-1].find(Indexed, ArgMin))
    
    Eq << Eq[-1].subs(i__.this.definition.reversed)
    
    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.domain_defined.delete)
    
    Eq.plausible = Eq.plausible.subs(Eq[-1])
    
    Eq << Eq.plausible.this.find(Norm).definition
    
    Eq.le = Eq[-1].this.find(Norm).definition
    
    Eq << Eq.le.find(mean, Indexed).this.definition
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << sets.eq.imply.forall.apply(Eq[-1])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.imply.le.st.argmin)
    
    Eq << Eq[-1].this.function.apply(algebra.le.imply.le.square)
    
    Eq << Eq[-1].this.find(Norm).definition
    
    Eq << Eq[-1].this.find(Norm).definition    
    
    Eq << Eq.le.find(mean).this.definition
    
    Eq << Eq[-1][i]
    
    Eq << Eq.le.rhs.find(mean).this.definition
    
    Eq << Eq[-1][i]
        
    Eq << Eq.le.subs(Eq[-1], Eq[-3])
    
    Eq << algebra.le.given.is_nonnegative.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.apply(algebra.add.to.sum)
    
    Eq << Eq[-1].this.lhs.function.expand()
    
    Eq << algebra.is_nonnegative.given.is_nonnegative.st.sum.apply(Eq[-1])

if __name__ == '__main__':
    prove()
