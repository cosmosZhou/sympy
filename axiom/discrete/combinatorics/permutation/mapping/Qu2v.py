from axiom.utility import prove, apply

from sympy import *
from axiom import discrete, algebra, sets

from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.permutation.index.eq import index_function


def predefined_symbols(n):
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    t = Symbol.t(integer=True)
    Q = Symbol.Q(LAMBDA[t:n + 1](conditionset(x[:n + 1], Equal(x[:n + 1].set_comprehension(), Interval(0, n, integer=True)) & Equal(x[n], t))))
    j = Symbol.j(integer=True)
    i = Symbol.i(integer=True)    
    w = Symbol.w(LAMBDA[j, i](Swap(n + 1, i, j)))
    
    return Q, w, x


def X_definition(n, w, x):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    index = index_function(n + 1)
    return Symbol("X", LAMBDA[j:n + 1](w[n, index[j](x[:n + 1], evaluate=False)] @ x[:n + 1])), index

    
@apply
def apply(n, u, v):
    Q, w, x = predefined_symbols(n)
    X, index = X_definition(n, w, x)
    return ForAll[x[:n + 1]:Q[u]](Contains(X[v], Q[v]) & Equal(x[:n + 1], w[n, index[u](X[v])] @ X[v])) 


@prove(surmountable=False)
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True, given=True)
    u = Symbol.u(domain=Interval(0, n, integer=True), given=True)
    v = Symbol.v(domain=Interval(0, n, integer=True))
    Eq << apply(n, u, v)

    w, i, j = Eq[0].lhs.args
    Q = Eq[2].lhs.base
    
    Eq << sets.imply.forall.conditionset.apply(Q[u])
    
    Eq.x_slice_last, Eq.x_slice_domain = algebra.forall_et.imply.forall.apply(Eq[-1])
    
    Eq << Eq.x_slice_domain.this.function.apply(discrete.combinatorics.permutation.index.eq, v)
    
    Eq.h_domain, Eq.x_h_equality = algebra.forall_et.imply.forall.apply(Eq[-1])
    
    hv = Eq.x_h_equality.function.lhs.indices[0]
    Eq << discrete.matrix.elementary.swap.invariant.permutation.basic.apply(n + 1, w=w)
    
    Eq << Subset(Eq[-2].limits[0][1], Eq[-1].rhs, plausible=True)    
    
    Eq << sets.subset.forall.imply.forall.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].subs(Eq[-1].rhs.this.definition)    
    
    Eq << Eq[-1].this.function.simplify()    
    
    Eq << Eq[-1].subs(i, n)
    
    Eq << Eq[-1].subs(j, hv)

    k = Eq[-1].function.lhs.function.arg.args[0].indices[-1]
    Eq.Xv_definition = Eq[1].subs(j, v)
    
    Eq << Eq.Xv_definition[k].apply(sets.eq.imply.eq.set_comprehension, (k, 0, n + 1))
    
    Eq.x_n1_set_comprehension = Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq.Xv_definition[n]
        
    Eq << Eq[0].subs(i, n).subs(j, hv)[n]
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << algebra.forall_eq.cond.imply.forall.subs.apply(Eq.x_h_equality, Eq[-1])    
    
    Eq << Eq[-1].this.function.apply(algebra.eq.imply.ou.two)
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1] & Eq.h_domain)
    
    Eq <<= Eq.x_n1_set_comprehension & Eq[-1] 
    
    Eq.Xv_in_Qv, Eq.x_eq_swap_Xv = algebra.forall_et.given.forall.apply(Eq[3])
    
    Eq << Eq.Xv_in_Qv.this.function.rhs.definition
    
    Eq.indexu_eq_indexu = Eq.x_eq_swap_Xv.function.rhs.args[0].indices[1].this.subs(Eq.Xv_definition)
    
    Eq.indexu_eq_indexv = Eq.x_slice_domain.this.function.apply(discrete.combinatorics.permutation.index.swap, u, v, w=w)
    
    Eq << Eq.x_slice_domain.this.function.apply(discrete.combinatorics.permutation.index.eq, u)
    
    Eq.indexu_contains, Eq.x_indexu_equality = algebra.forall_et.imply.forall.apply(Eq[-1], simplify=None)
    
    Eq.equality_of_indexu_and_n = (Eq.x_indexu_equality & Eq.x_slice_last).this.function.apply(algebra.eq.eq.imply.eq.transit)

    i = Symbol.i(domain=Interval(0, n, integer=True))
    j = Symbol.j(domain=Interval(0, n, integer=True))
    
    Eq << Eq.x_slice_domain.this.function.apply(discrete.combinatorics.permutation.index.kronecker_delta.indexOf, i, j)

    x = Eq[-1].variable.base
    Eq.ou = Eq[-1].subs(i, x[n])
    
    Eq << Exists(Eq.ou.function.args[0], *Eq.ou.limits, plausible=True)
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq.x_slice_last, Eq[-1])
    
    Eq <<= Eq.ou & ~Eq[-1]
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1], index=1)
    
    m = Symbol.m(domain=Interval(0, n, integer=True))
    Eq.indexOf_indexed = Eq.x_slice_domain.this.function.apply(discrete.combinatorics.permutation.index.indexOf_indexed, j=m)
    
    Eq << Eq.indexOf_indexed.subs(m, n)
    
    Eq << (Eq[-2] & Eq[-1]).this.function.apply(algebra.eq.eq.imply.eq.subs)
    
    Eq.ou = Eq[-1].subs(j, Eq.equality_of_indexu_and_n.function.lhs)

    Eq << Exists(Eq.ou.function.args[0], *Eq.ou.limits, plausible=True)

    Eq << algebra.forall.exists.imply.exists_et.apply(Eq.x_indexu_equality, Eq[-1])
    
    Eq <<= Eq.ou & ~Eq[-1]
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1], index=1)
    
    Eq.ou = Eq.indexOf_indexed.subs(m, Eq.equality_of_indexu_and_n.function.lhs.indices[0])
    
    Eq << Exists(Eq.ou.function.args[0], *Eq.ou.limits, plausible=True)    
    
    Eq <<= Eq.indexu_contains & Eq[-1]
    
    Eq.index_equality = algebra.forall_et.imply.forall.apply(Eq.ou & ~Eq[-1], index=1)
    
    Eq << discrete.combinatorics.permutation.is_nonemptyset.Qu.apply(n, u)
    
    Eq <<= Eq[-3] & Eq.index_equality
    
    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.subs)
    
    Eq <<= Eq[-1] & Eq.equality_of_indexu_and_n
    
    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.subs)
    
    Eq <<= Eq.indexu_eq_indexv & Eq[-1]
    
    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.subs, swap=True, reverse=True)
    
    Eq << algebra.forall_eq.cond.imply.forall.subs.apply(Eq[-1], Eq.indexu_eq_indexu)
    
    Eq <<= Eq.x_eq_swap_Xv & Eq[-1]
    
    Eq << Eq[-1].this.function.apply(algebra.et.given.et.subs.eq, index=0)
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.Xv_definition)

    Eq << discrete.matrix.elementary.swap.multiply.left.apply(x[:n + 1], i=n, j=Eq.h_domain.lhs, w=w)    
    
    Eq << Eq[-2].subs(Eq[-1])
    
    
if __name__ == '__main__':
    prove()
