from axiom.utility import prove, apply

from sympy import *
from sympy.matrices.expressions.matexpr import Swap

from axiom import algebre, discrete, sets


@apply
def apply(n, w=None):
    domain = Interval(0, n - 1, integer=True)
    t = Symbol.t(domain=domain)
    i = Symbol.i(domain=domain)
    j = Symbol.j(domain=domain)
    assert n >= 2
    if w is None:
        w = Symbol.w(LAMBDA[j, i](Swap(n, i, j)))
    
    return ForAll(Equality(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain // {i, t}))


@prove
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
    
    Eq << Eq[-1].this.rhs.function.args[1].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.function.args[-1].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs().function.simplify(wrt=True)    
    
    Eq << Eq[-1].this.rhs.function.args[-1].expr.astype(Plus)
    
    Eq << Eq[-1].this.rhs().function.apply(algebre.piecewise.swap.back)
    
    Eq << Eq[-1].this.rhs().function.args[2].cond.simplify()
    
    Eq << Eq[-1].this.rhs.function.args[2].cond.apply(sets.contains.astype.ou)
    
    Eq << Eq[-1].this.rhs().function.apply(algebre.piecewise.invert, index=1)
    
    Eq << Eq[-1].this.rhs.function.apply(algebre.piecewise.subs, index=2)
    
    Eq << algebre.cond.imply.forall.restrict.apply(Eq[-1], (j,))

    Eq << algebre.cond.imply.forall.restrict.apply(Eq[-1], Eq[1].limits[0])
    
    Eq << Eq[-1].this().function.simplify()
        
    Eq << (w[t, i] @ Eq[-1]).this.function.rhs.subs(w[t, i].this.definition)
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    Eq << Eq[-1].this().function.rhs().function.simplify(wrt=True)
    
    Eq << Eq[-1].this().function.rhs().function.args[-1].expr.args[1].apply(algebre.piecewise.swap.front)
    
    Eq << Eq[-1].this.function.rhs.function.astype(KroneckerDelta)
    
    Eq.www_expansion = Eq[-1].this().function.rhs.function.simplify()
    
    j = j.unbounded
    Eq << (w[i, j] @ x).this.subs(w[i, j].this.definition).this.rhs.expand()
    
    Eq << Eq[-1].this(j).rhs().function.simplify(wrt=True)
    
    Eq << Eq[-1].this.rhs.function.astype(KroneckerDelta)

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq.www_expansion.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(discrete.matrix.independence.rmatmul_equal)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
