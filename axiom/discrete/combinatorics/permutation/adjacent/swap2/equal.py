from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy import ForAll, LAMBDA
from sympy import Symbol
from axiom import discrete

@apply(imply=True)
def apply(n, w=None):
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    assert n >= 2
    if w is None:
        w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
    
    return ForAll(Equality(w[0, i] @ w[0, j] @ w[0, i], w[i, j]), (j, Interval(1, n - 1, integer=True) - i.set))


@prove
def prove(Eq):   
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    assert 0 in Interval(0, n - 1, integer=True)
    Eq << apply(n)
    w = Eq[0].lhs.base
    Eq << discrete.combinatorics.permutation.adjacent.swap2.equal_general.apply(n, w=w)
    
    w_ti, *_ = Eq[-1].function.lhs.args
    t, i = w_ti.indices
     
    Eq << Eq[-1].subs(t, 0)
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
