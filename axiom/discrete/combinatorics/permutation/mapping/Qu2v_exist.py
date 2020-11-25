from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy.core.numbers import oo
from sympy.sets.conditionset import conditionset
from sympy.sets.sets import Interval
from sympy import Symbol
from sympy.concrete.expr_with_limits import LAMBDA, ForAll, Exists
from axiom import discrete, algebre, sets
from sympy.sets.contains import Contains, Subset
from sympy.matrices.expressions.matexpr import Swap


def predefined_symbols(n):
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    t = Symbol.t(integer=True)
    Q = Symbol.Q(definition=LAMBDA[t:n + 1](conditionset(x[:n + 1], Equality(x[:n + 1].set_comprehension(), Interval(0, n, integer=True)) & Equality(x[n], t))))
    j = Symbol.j(integer=True)
    i = Symbol.i(integer=True)    
    w = Symbol.w(definition=LAMBDA[j:n + 1, i:n + 1](Swap(n + 1, i, j)))
    
    x_quote = Symbol("x'", definition=w[n, j] @ x[:n + 1])
    return Q, w, x, x_quote, j

    
@plausible
def apply(n, u, v):
    Q, w, x, x_quote, j = predefined_symbols(n)
    return ForAll[x[:n + 1]:Q[u]](Exists[j:0:n](Contains(x_quote, Q[v])))


from axiom.utility import check


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    u = Symbol.u(domain=Interval(0, n, integer=True))
    v = Symbol.v(domain=Interval(0, n, integer=True))
    Eq << apply(n, u, v)
    
    w, i, j = Eq[0].lhs.args
    Q = Eq[2].lhs.base
    
    Eq << sets.imply.conditionset.apply(Q[u]).split()
    
    Eq.x_j_equality = Eq[-1].apply(discrete.combinatorics.permutation.index.exists, v)    
    
    Eq << Eq.x_j_equality.this.function.limits_subs(Eq.x_j_equality.function.variable, j)
    
    Eq << algebre.matrix.elementary.swap.invariant.permutation.apply(n + 1, w=w)
    
    Eq << Subset(Eq[-2].limits[0][1], Eq[-1].rhs, plausible=True)    
    
    Eq << sets.subset.forall.imply.forall.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].subs(Eq[-1].rhs.this.definition)
    
    Eq << Eq[-1].subs(i, n)
    
    k = Eq[-1].function.lhs.function.arg.args[0].indices[-1]
    Eq << Eq[1][k].set.union_comprehension((k, 0, n))
    
    Eq.x_n1_set_comprehension = Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[1][n]
        
    Eq << Eq[0].subs(i, n)[n]
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].subs(Eq.x_j_equality)
    
    Eq << Eq[-1].this.function().function.rhs.args[0].simplify()
    
    Eq <<= Eq.x_n1_set_comprehension & Eq[-1] 
    
    Eq << Eq[3].definition

    
if __name__ == '__main__':
    prove(__file__)
