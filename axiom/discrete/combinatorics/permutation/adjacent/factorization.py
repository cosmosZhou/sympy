from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom import discrete, sets, algebre


@apply
def apply(n):
    i = Symbol.i(integer=True)
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    b = Symbol.b(integer=True, shape=(oo,), nonnegative=True)
    
    return ForAll[p[:n]:P](Exists[b[:n]](Equality(p[:n], LAMBDA[i:n](i) @ MatProduct[i:n](Swap(n, i, b[i])))))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    Eq << apply(n)
    
    i = Symbol.i(integer=True)    
    p = Eq[1].variable.base
    b = Eq[1].function.variable.base
    
    Eq.hypothesis = Eq[1].subs(Eq[0]).copy(plausible=True)
    
    Eq.initial = Eq.hypothesis.subs(n, 2)
        
    Eq << Eq.initial.doit(deep=True)    

    p0 = Eq[-1].variable
    Eq << Eq[-1].apply(algebre.exists.given.exists.subs, b[:2], Matrix((0, KroneckerDelta(p0, 0))), depth=1)
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    Eq << Eq[-1].this.function.rhs[0].simplify()
    
    Eq.equation = Eq[-1].this.function.rhs[1].simplify()
    
    Eq.limits_assertion = algebre.imply.forall.limits_assert.apply(Eq.equation.limits)
    
    Eq << Eq.limits_assertion.apply(sets.equal.imply.equal.where.finiteset.add)
    
    Eq.p1_equality = Eq[-1].this.function - p0
    
    Eq << Eq.equation.subs(Eq.p1_equality) 
    
    Eq.premier, Eq.second = Eq[-1].split()
    
    Eq << Eq.limits_assertion.split()
    
    Eq << Eq[-2].apply(sets.contains.imply.equal.kronecker_delta.zero).reversed
    
    Eq << Eq[-1].subs(Eq.p1_equality)
    
    Eq << Eq.premier.subs(Eq.second.reversed)
    
    Eq.induction = Eq.hypothesis.subs(n, n + 1)
    
    Eq << Eq.induction.function.function.rhs.args[1].this.bisect(Slice[-1:])

    Eq << discrete.matrix.elementary.swap.concatenate_product.apply(n, n, b)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq.induction.subs(Eq[-1])
    
    Eq << Eq[-1].this.function.function.rhs.args[0].bisect(Slice[-1:])
    
    Eq << MatMul(*Eq[-1].function.function.rhs.args[:2]).this.expand()
    
    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq.deduction = Eq[-1].this.function.function @ Eq[-1].function.function.rhs.args[1]
    
    Eq << discrete.combinatorics.permutation.exists.basic.apply(n + 1)
    
    Eq << Eq[-1].this.function.limits_subs(Eq[-1].function.variable, b[n])
    
    Eq.exists_n = Eq[-1].subs(Eq[-1].limits[0][1].this.definition)
    
    p_quote = Symbol.p_quote(Eq.deduction.function.function.lhs)
    
    Eq.p_quote_definition = p_quote.this.definition
    
    Eq.deduction = Eq.deduction.subs(Eq.p_quote_definition.reversed)
    
    Eq << Eq.p_quote_definition.lhs[n].this.definition
    
    Eq << Eq[-1].this.rhs.args[1].function.astype(KroneckerDelta)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].subs(Eq.exists_n)
    
    Eq << Eq[-1].this.function().function.rhs.simplify()
    
    Eq.exists_n_plausible = Eq[-1].apply(sets.exists.imply.exists.amplify, wrt=Eq[-1].function.variable, depth=1)
    
    Eq << discrete.matrix.elementary.swap.invariant.permutation.basic.apply(n + 1, left=False)
    
    i, j = Eq[-1].function.lhs.args[1].indices
    Eq << Eq[-1].subs(Eq[-1].function.lhs.args[1].this.definition)
    
    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.exists_n_plausible.variable).subs(Eq.p_quote_definition.reversed)
    
    Eq << Eq[-1].subs(Eq[-1].function.rhs.this.definition)
    
    Eq << Eq.exists_n_plausible.apply(discrete.combinatorics.permutation.pop_back.interval, Eq[-1])
    
    Eq << Eq.hypothesis.subs(Eq.hypothesis.variable, p_quote[:n])

    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << Eq.p_quote_definition.lhs.this.bisect(Slice[-1:])
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].subs(Eq.exists_n_plausible)   
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.condition.sufficient.imply.condition.induction.apply(Eq.initial, Eq[-1], n=n, start=2)
    
    Eq << Eq[1].subs(Eq[0])

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
