from sympy import *
from axiom.utility import prove, apply

from axiom import discrete, sets, algebra
from axiom.discrete.combinatorics.permutation.mapping.Qu2v import predefined_symbols


@apply
def apply(n, u, v):
    Q, w, x = predefined_symbols(n)
    j = w.definition.variables[0]
    x_quote = Symbol("x'", w[n, j] @ x[:n + 1])
    return ForAll[x[:n + 1]:Q[u]](Exists[j:0:n + 1](Contains(x_quote, Q[v])))


@prove(surmountable=False)
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    u = Symbol.u(domain=Interval(0, n, integer=True))
    v = Symbol.v(domain=Interval(0, n, integer=True))
    Eq << apply(n, u, v)
    
    w, i, j = Eq[0].lhs.args
    Q = Eq[2].lhs.base
    
    Eq << sets.imply.forall.conditionset.apply(Q[u])
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1])
    
    Eq.x_j_equality = Eq[-1].this.function.apply(discrete.combinatorics.permutation.index.exists, v)    
    
    Eq << Eq.x_j_equality.this.function.limits_subs(Eq.x_j_equality.function.variable, j)
    
    Eq << discrete.matrix.elementary.swap.invariant.permutation.basic.apply(n + 1, w=w)
    
    Eq << Subset(Eq[-2].limits[0][1], Eq[-1].rhs, plausible=True)    
    
    Eq << sets.subset.forall.imply.forall.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << Eq[-1].subs(i, n)
    
    k = Eq[-1].function.lhs.function.arg.args[0].indices[-1]
    
    Eq << Eq[1][k].apply(sets.eq.imply.eq.set_comprehension, (k, 0, n + 1))
    
    Eq.x_n1_set_comprehension = Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[1][n]
        
    Eq << Eq[0].subs(i, n)[n]
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << algebra.forall_exists_eq.cond.imply.forall_exists.subs.apply(Eq.x_j_equality, Eq[-1])
    
    Eq << Eq[-1].this.function().function.rhs.args[0].simplify()
    
    Eq <<= Eq.x_n1_set_comprehension & Eq[-1] 
    
    Eq << Eq[3].this.function.function.rhs.definition

    
if __name__ == '__main__':
    prove()
