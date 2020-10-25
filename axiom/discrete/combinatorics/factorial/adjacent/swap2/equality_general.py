from sympy.core.relational import Equality

from axiom.utility import check, plausible
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import ForAll, LAMBDA
from axiom import algebre


@plausible
def apply(n):
    domain = Interval(0, n - 1, integer=True)
    t = Symbol.t(domain=domain)
    i = Symbol.i(domain=domain)
    j = Symbol.j(domain=domain)
    assert n >= 2
    w = Symbol.w(integer=True, shape=(n, n, n, n), definition=LAMBDA[j, i](Swap(n, i, j)))
    
    return ForAll(Equality(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain - {i, t}))


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    Eq << apply(n)
    
    i, _ = Eq[-1].rhs.indices
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    w = Eq[0].lhs.base
    
    t = Eq[1].function.lhs.args[0].indices[0]
    
    p = Symbol.p(complex=True)
    
    x = LAMBDA[i:n](p ** i)
    
    eq = Eq[0].subs(i, t)
    
    assert eq.lhs.args[-1] == j
    
    assert eq.rhs.args[-1] == j
    
    Eq << (w[t, i] @ x).this.subs(Eq[0].subs(i, t).subs(j, i))
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs().function.simplify()
    
    Eq << (w[t, j] @ Eq[-1]).this.rhs.subs(w[t, j].this.definition)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs().function.simplify(wrt=True)

    Eq << Eq[-1].forall((j,))

    Eq << Eq[-1].forall(Eq[1].limits[0])
        
    Eq << (w[t, i] @ Eq[-1]).this.function.rhs.subs(w[t, i].this.definition)
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    Eq << Eq[-1].this().function.rhs().function.simplify(wrt=True)
    
    Eq << Eq[-1].this.function.rhs.function.as_KroneckerDelta()
    
    Eq.www_expansion = Eq[-1].this().function.rhs.function.simplify()

    j = j.unbounded
    Eq << (w[i, j] @ x).this.subs(w[i, j].this.definition).this.rhs.expand()
    
    Eq << Eq[-1].this(j).rhs().function.simplify(wrt=True)
    
    Eq << Eq[-1].this.rhs.function.as_KroneckerDelta()

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq.www_expansion.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(algebre.matrix.independence.rmatmul_equality)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
