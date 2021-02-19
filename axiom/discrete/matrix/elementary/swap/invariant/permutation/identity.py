from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import prove, apply
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import ForAll, LAMBDA
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from sympy.concrete.products import MatProduct
from sympy import Symbol
from axiom import discrete, algebre


@apply
def apply(m, d, w=None):
    n = d.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    assert m >= 0
    if w is None:
        w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
        
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    x = x[:n]
    
    P = Symbol.P(etype=dtype.integer * n, definition=conditionset(x, Equality(x.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return Contains(LAMBDA[i:n](i) @ MatProduct[i:m](w[i, d[i]]), P)


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    m = Symbol.m(integer=True, nonnegative=True)
    d = Symbol.d(shape=(n,), integer=True, nonnegative=True)
    
    Eq << apply(m, d)
    
    Eq << discrete.matrix.elementary.swap.invariant.permutation.general.apply(m, d)
    
    Eq << Eq[-1].subs(Eq[-1].variable, Eq[2].lhs.args[0]).split()

    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].this.lhs.simplify()
    
    
            
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html


