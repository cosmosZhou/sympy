from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.numbers import oo
from sympy.sets.conditionset import conditionset
from sympy.sets.sets import Interval
from sympy import Symbol
from sympy import LAMBDA, ForAll
from axiom import discrete, algebre, sets
from sympy.sets.contains import Contains, Subset
from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.permutation.index.equality import index_function


def predefined_symbols(n):
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    t = Symbol.t(integer=True)
    Q = Symbol.Q(definition=LAMBDA[t:n + 1](conditionset(x[:n + 1], Equality(x[:n + 1].set_comprehension(), Interval(0, n, integer=True)) & Equality(x[n], t))))
    j = Symbol.j(integer=True)
    i = Symbol.i(integer=True)    
    w = Symbol.w(definition=LAMBDA[j:n + 1, i:n + 1](Swap(n + 1, i, j)))
    
    return Q, w, x


def X_definition(n, w, x):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    index = index_function(n + 1)
    return Symbol("X", definition=LAMBDA[j:n + 1](w[n, index[j](x[:n + 1], evaluate=False)] @ x[:n + 1])), index

    
@plausible
def apply(n, u, v):
    Q, w, x = predefined_symbols(n)
    X, index = X_definition(n, w, x)
    return ForAll[x[:n + 1]:Q[u]](Contains(X[v], Q[v]) & Equality(x[:n + 1], w[n, index[u](X[v])] @ X[v])) 


from axiom.utility import check


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    u = Symbol.u(domain=Interval(0, n, integer=True))
    v = Symbol.v(domain=Interval(0, n, integer=True))
    Eq << apply(n, u, v)

    w, i, j = Eq[0].lhs.args
    Q = Eq[2].lhs.base
    
    Eq.x_slice_last, Eq.x_slice_domain = sets.imply.forall.conditionset.apply(Q[u]).split()
    
    Eq << Eq.x_slice_domain.apply(discrete.combinatorics.permutation.index.equality, v)
    Eq.h_domain, Eq.x_h_equality = Eq[-1].split()
    
    hv = Eq.x_h_equality.function.lhs.indices[0]
    Eq << discrete.matrix.elementary.swap.invariant.permutation.apply(n + 1, w=w)
    
    Eq << Subset(Eq[-2].limits[0][1], Eq[-1].rhs, plausible=True)    
    
    Eq << sets.subset.forall.imply.forall.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].subs(Eq[-1].rhs.this.definition)
    
    Eq << Eq[-1].subs(i, n)
    
    Eq << Eq[-1].subs(j, hv)

    k = Eq[-1].function.lhs.function.arg.args[0].indices[-1]
    Eq.Xv_definition = Eq[1].subs(j, v)
    
    Eq << Eq.Xv_definition[k].set.union_comprehension((k, 0, n))
    
    Eq.x_n1_set_comprehension = Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq.Xv_definition[n]
        
    Eq << Eq[0].subs(i, n).subs(j, hv)[n]
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].subs(Eq.x_h_equality)
    
    Eq << Eq[-1].apply(algebre.equality.imply.ou.two)
    
    Eq << (Eq[-1] & Eq.h_domain).split()
    
    Eq <<= Eq.x_n1_set_comprehension & Eq[-1] 
    
    Eq.Xv_in_Qv, Eq.x_eq_swap_Xv = Eq[3].split()
    
    Eq << Eq.Xv_in_Qv.definition
    
    Eq.indexu_eq_indexu = Eq.x_eq_swap_Xv.function.rhs.args[0].indices[1].this.subs(Eq.Xv_definition)
    
    Eq.indexu_eq_indexv = Eq.x_slice_domain.apply(discrete.combinatorics.permutation.index.swap, u, v, w=w)
    
    Eq.indexu_contains, Eq.x_indexu_equality = Eq.x_slice_domain.apply(discrete.combinatorics.permutation.index.equality, u).split()
    
    Eq.equality_of_indexu_and_n = Eq.x_indexu_equality + Eq.x_slice_last.reversed

    i = Symbol.i(domain=Interval(0, n, integer=True))
    j = Symbol.j(domain=Interval(0, n, integer=True))
    
    Eq << Eq.x_slice_domain.apply(discrete.combinatorics.permutation.index.kronecker_delta.indexOf, i, j)
        
    x = Eq[-1].variable.base
    Eq << Eq[-1].subs(i, x[n]).split()
    
    Eq << Eq[-2].subs(Eq.x_slice_last)
    
    m = Symbol.m(domain=Interval(0, n, integer=True))
    Eq.indexOf_indexed = Eq.x_slice_domain.apply(discrete.combinatorics.permutation.index.indexOf_indexed, j=m)
    
    Eq << Eq.indexOf_indexed.subs(m, n)
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].subs(j, Eq.equality_of_indexu_and_n.function.lhs).split()
    
    Eq << Eq[-2].subs(Eq.x_indexu_equality)
    
    Eq.notcontains, Eq.index_equality = Eq.indexOf_indexed.subs(m, Eq.equality_of_indexu_and_n.function.lhs.indices[0]).split()
    
    Eq <<= Eq.indexu_contains & Eq.notcontains
    
    Eq << discrete.combinatorics.permutation.is_nonemptyset.Qu.apply(n, u)
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-3].subs(Eq.index_equality)
    
    Eq << Eq[-1].subs(Eq.equality_of_indexu_and_n)

    Eq << Eq.indexu_eq_indexv.subs(Eq[-1].reversed)
    
    Eq << Eq.indexu_eq_indexu.subs(Eq[-1])
    
    Eq << Eq.x_eq_swap_Xv.subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.Xv_definition)
    
    Eq << discrete.matrix.elementary.swap.multiply.left.apply(x[:n + 1], i=n, j=Eq.h_domain.lhs, w=w)    

    Eq << Eq[-2].subs(Eq[-1])
    
    
if __name__ == '__main__':
    prove(__file__)
