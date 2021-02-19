from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from axiom import discrete


@apply
def apply(n, w=None, left=True, P=None):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    if w is None:
        w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
        
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    x = x[:n]
    
    if P is None:
        P = Symbol.P(etype=dtype.integer * n, definition=conditionset(x, Equality(x.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    if left:
        return ForAll[x:P](Contains(w[i, j] @ x, P))
    else:
        return ForAll[x:P](Contains(x @ w[i, j], P))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    Eq << apply(n)
    
    w = Eq[0].lhs.base
    
    x = Eq[2].variable
    
    Eq << discrete.matrix.elementary.swap.invariant.set_comprehension.union_comprehension.apply(x, w)
    
    Eq << Eq[2].this.function.rhs.definition.subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[1])

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
