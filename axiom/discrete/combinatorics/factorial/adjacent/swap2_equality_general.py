from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import ForAll, Ref
from axiom import Algebre


@plausible
def apply(n):
    domain = Interval(0, n - 1, integer=True)
    t = Symbol('t', domain=domain)
    i = Symbol('i', domain=domain)
    j = Symbol('j', domain=domain)
    assert n >= 2
    w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    return ForAll(Equality(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain - {i, t}))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    Eq << apply(n)
    
    i, _ = Eq[-1].rhs.indices
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    w = Eq[0].lhs.base
    
    t = Eq[1].function.lhs.args[0].indices[0]
    
    p = Symbol('p')
    
    x = Ref[i:n](p ** i)
    
    eq = Eq[0].subs(i, t)
    
    assert eq.lhs.args[-1] == j
    
    assert eq.rhs.args[-1] == j
    
    Eq << (w[t, i] @ x).this.subs(Eq[0].subs(i, t).subs(j, i))
    
    Eq << Eq[-1].this.rhs.expand().simplify(deep=True)
    
    Eq << w[t, j] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].forall(j)
    
    Eq << Eq[-1].forall(*Eq[1].limits[0])
    
    Eq << Eq[-1].this.function.rhs.simplify(deep=True)
    
    Eq << w[t, i] @ Eq[-1]
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    Eq << Eq[-1].this.simplify(deep=True)

    Eq << Eq[-1].this.function.rhs.function.asKroneckerDelta()
    
    Eq.www_expansion = Eq[-1].this.simplify(deep=True)
    
    Eq << (w[i, j.unbounded] @ x).this.expand().simplify(deep=True)
    
    Eq << Eq[-1].simplify(wrt=j.unbounded)
    
    Eq << Eq[-1].this.rhs.function.asKroneckerDelta()
    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq.www_expansion.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(Algebre.matrix.independence.rmatmul_equality)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
