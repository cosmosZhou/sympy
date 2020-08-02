from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import Forall
from axiom import Algebre


@plausible
def apply(n, w=None):
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    assert n >= 2
    if w is None:
        w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
    
    return Forall(Equality(w[0, i] @ w[0, j] @ w[0, i], w[i, j]), (j, Interval(1, n - 1, integer=True) - i.set))


@check
def prove(Eq):    
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    assert 0 in Interval(0, n - 1, integer=True)
    
    Eq << apply(n)
    
    i, _ = Eq[-1].rhs.indices
    
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    w = Eq[0].lhs.base
    
    p = Symbol('p')
    
    x = Ref[i:n](p ** i)
    Eq << identity(w[0, i] @ x).subs(Eq[0].subs(i, 0).subs(j, i))
    Eq << Eq[-1].this.rhs.expand().simplify(deep=True)
    
    Eq << w[0, j] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].forall(j, Interval(1, n - 1, integer=True) - i.set)
    
    Eq << Eq[-1].this.function.rhs.simplify(deep=True)
    
    Eq << w[0, i] @ Eq[-1]
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    Eq << Eq[-1].this.simplify(deep=True)

    Eq << Eq[-1].this.function.rhs.function.asKroneckerDelta()
    
    Eq.www_expansion = Eq[-1].this.simplify(deep=True)

    Eq << identity(w[i, j.unbounded] @ x).expand().simplify(deep=True)
    
    Eq << Eq[-1].simplify(wrt=j.unbounded)
    
    Eq << Eq[-1].this.rhs.function.asKroneckerDelta()
    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq.www_expansion.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(Algebre.matrix.independence.rmatmul_equality)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
