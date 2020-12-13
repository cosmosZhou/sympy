from sympy.core.relational import Unequal
from axiom.utility import plausible
from sympy.sets.sets import Interval
from sympy import Symbol
from sympy import LAMBDA, Exists
from axiom import algebre, discrete
from sympy.sets.contains import Contains
from axiom.discrete.combinatorics.permutation.mapping.Qu2v import predefined_symbols

from sympy.matrices.expressions.matexpr import Swap

    
@plausible
def apply(n, u=None):
    Q, w, x = predefined_symbols(n)
    if u is None:
        u = Q.definition.variable
    return Unequal(Q[u], Q[u].etype.emptySet) 


from axiom.utility import check


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    i = Symbol.i(integer=True)
    Q, t = Eq[0].lhs.args
    _t = t.copy(domain=Interval(0, n, integer=True))
    a = Symbol.a(definition=LAMBDA[i:n + 1](i) @ Swap(n + 1, n, _t))
    Eq << a.this.definition
    
    Eq << a[n].this.definition.this.rhs.expand()    
    
    Eq << discrete.matrix.elementary.swap.invariant.set_comprehension.definition.apply(a)
    
    x = Eq[0].rhs.variable.base
    Eq << Exists[x[:n + 1]](Contains(x[:n + 1], Q[_t]), plausible=True)
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << Eq[-1].subs(x[:n + 1], a).split()
    
    Eq << Eq[-2].simplify()
    
    Eq << Eq[-1].forall((_t,))

    
if __name__ == '__main__':
    prove(__file__)
