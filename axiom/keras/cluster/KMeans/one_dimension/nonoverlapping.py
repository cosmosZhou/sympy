from sympy import *
from axiom.utility import prove, apply
from axiom import keras, algebra, sets
import axiom


# wi is of etype integer
def mean(wi, x):
    j = Symbol.j(integer=True)    
    return Sum[j:wi](x[j]) / abs(wi)


def __getitem__(self, indices):
    if isinstance(indices, (tuple, list)):
        return Indexed(self, *indices)
    return Indexed(self, indices)


mean = Function.mean(shape=property(lambda self: self.args[1].shape[1:]), real=True, eval=mean, __getitem__=__getitem__)


# c is a list of vectors, (k, n)
# return a list of set of integers, (k,)
def cluster(w, x):
    i = Symbol.i(integer=True)    
    k = w.shape[0]
    j = Symbol.j(integer=True)
    
    return LAMBDA[i:k](conditionset(j, Equal(ArgMin[i](Abs(x[j] - mean(w[i], x))), i)))
    

cluster = Function.cluster(eval=cluster, __getitem__=__getitem__)


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
        
    return Equal(Sum[i](abs(w_[i])), M), Equal(UNION[i](w_[i]), M_interval)


@prove
def prove(Eq):
    M = Symbol.M(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    k = Symbol.k(domain=Interval(0, M - 1, integer=True))
        
    x = Symbol.x(real=True, shape=(M,))
    w = Symbol.omega(shape=(k,), etype=dtype.integer, emptyset=False)
    
    Eq << apply(Equal(Sum[i](abs(w[i])), M), Equal(UNION[i](w[i]), k.domain), x=x)

    Eq << Eq[0].this.rhs.definition
    
    Eq.omega_i_definition0 = Eq[-1][i]
    
    Eq.omega_i_definition = Eq.omega_i_definition0.this.rhs.apply(sets.conditionset.rewrite.domain_defined)
    
    j = Eq.omega_i_definition.rhs.variable
    Eq << sets.eq.given.sufficient.apply(Eq[4], wrt=j)
    
    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.exists_contains.st.union_comprehension), \
    Eq[-1].this.rhs.apply(sets.contains.given.exists_contains.st.union_comprehension)
    
    Eq <<= Eq[-2].subs(Eq.omega_i_definition), Eq[-1].subs(Eq.omega_i_definition0)
    
    Eq << Eq[-2].this.lhs.function.simplify()
    
    Eq << Eq[-1].this.rhs.function.simplify()
    
    w_ = Eq.omega_i_definition.lhs.base
    
    k_ = Symbol.k(integer=True)
    
    Eq.nonoverlapping = ForAll[i:k_](Equal(w_[i] & w_[k_], w_[i].etype.emptySet), plausible=True)
    
    Eq << Eq.omega_i_definition0.subs(i, k_)
    
    Eq << sets.eq.eq.imply.eq.intersect.apply(Eq.omega_i_definition0, Eq[-1])
    
    Eq << Eq[-1].this.find(And).apply(sets.eq.eq.imply.contains.finiteset)
    
    Eq << Eq.nonoverlapping.subs(Eq[-1])
    
    Eq << Eq[-1].this().find(Intersection).simplify()
    
    Eq << sets.forall_is_emptyset.imply.eq.nonoverlapping.util.intlimit.apply(Eq.nonoverlapping, k)
    
    Eq << Eq[-1].this.find(UNION).limits_subs(k_, i)
    
    Eq << Eq[-1].this.rhs.limits_subs(k_, i)
    
    Eq << Eq[-1].subs(Eq[4]).reversed


if __name__ == '__main__':
    prove()
