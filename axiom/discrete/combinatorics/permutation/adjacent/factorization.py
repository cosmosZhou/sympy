from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom import discrete, sets, algebra


@apply
def apply(n):
    i = Symbol.i(integer=True)
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    b = Symbol.b(integer=True, shape=(oo,), nonnegative=True)
    
    return ForAll[p[:n]:P](Exists[b[:n]](Equal(p[:n], LAMBDA[i:n](i) @ MatProduct[i:n](Swap(n, i, b[i])))))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True), given=False)
    
    Eq << apply(n)
    
    b = Eq[1].function.variable.base
    
    Eq.hypothesis = Eq[1].subs(Eq[0]).copy(plausible=True)
    
    Eq.initial = Eq.hypothesis.subs(n, 2)
        
    Eq << Eq.initial.doit(deep=True)    

    p0 = Eq[-1].variable
    Eq << Eq[-1].this.function.apply(algebra.exists.given.exists.subs, b[:2], Matrix((0, KroneckerDelta(p0, 0))))
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    Eq << Eq[-1].this.function.rhs[0].simplify()
    
    Eq.equation = Eq[-1].this.function.rhs[1].simplify()
    
    Eq.limits_assertion = algebra.imply.forall.limits_assert.apply(Eq.equation.limits)
    
    Eq << Eq.limits_assertion.this.function.apply(sets.eq.imply.eq.split.finiteset.add)
    
    Eq.p1_equality = Eq[-1].this.function - p0
    
    Eq <<= Eq.equation & Eq.p1_equality
    
    Eq << Eq[-1].this.function.apply(algebra.et.given.et.subs.eq, index=1)
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.given.et.split.dense_matrix)
    
    Eq.premier, Eq.second = algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << Eq.limits_assertion.this.function.apply(sets.eq.imply.et.split.finiteset)    

    Eq << algebra.forall_et.imply.forall.apply(Eq[-1])
    
    Eq << Eq[-2].this.function.apply(sets.contains.imply.eq.kronecker_delta.zero).reversed
    
    Eq << -(Eq.premier - 1)
    
    Eq.induct = Eq.hypothesis.subs(n, n + 1)
    
    Eq << Eq.induct.function.function.rhs.args[1].this.bisect(Slice[-1:])
    
    Eq << discrete.matrix.elementary.swap.concatenate_product.apply(n, n, b)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq.induct.subs(Eq[-1])
    
    Eq << Eq[-1].this.function.function.rhs.args[0].bisect(Slice[-1:])
    
    Eq << MatMul(*Eq[-1].function.function.rhs.args[:2]).this.expand()
    
    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq.deduction = Eq[-1].this.function.function @ Eq[-1].function.function.rhs.args[1]
    
    Eq << discrete.combinatorics.permutation.exists.basic.apply(n + 1)
    
    Eq << Eq[-1].this.function.limits_subs(Eq[-1].function.variable, b[n])
    
    Eq.exists_n = Eq[-1].this.limits[0][1].definition
    
    p_quote = Symbol.p_quote(Eq.deduction.function.function.lhs)
    
    Eq.p_quote_definition = p_quote.this.definition
    
    Eq.deduction = Eq.deduction.subs(Eq.p_quote_definition.reversed)
    
    Eq << Eq.p_quote_definition.lhs[n].this.definition
    
    Eq << Eq[-1].this.rhs.args[1].function.astype(KroneckerDelta)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << algebra.forall_exists_eq.cond.imply.forall_exists.subs.apply(Eq.exists_n, Eq[-1])
    
    Eq << Eq[-1].this.function().function.rhs.simplify()
    
    Eq.exists_n_plausible = Eq[-1].this.function.apply(sets.exists.imply.exists.limits.relax, wrt=Eq[-1].function.variable)

    Eq << discrete.matrix.elementary.swap.invariant.permutation.basic.apply(n + 1, left=False)
        
    i, j = Eq[-1].find(Indexed).indices
    Eq << Eq[-1].this.find(Indexed).definition
    
    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.exists_n_plausible.variable).subs(Eq.p_quote_definition.reversed)
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << Eq[-1].this.limits[0][1].definition
    
    Eq <<= Eq.exists_n_plausible & Eq[-1]
    
    Eq << Eq[-1].this.function.apply(algebra.cond.exists.imply.exists_et)
    
    Eq << Eq[-1].this.function.function.apply(discrete.combinatorics.permutation.pop_back.interval)
    
    Eq << algebra.forall.imply.ou.subs.apply(Eq.hypothesis, Eq.hypothesis.variable, p_quote[:n])
    
    Eq << algebra.cond.forall.imply.forall_et.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.function.apply(algebra.exists.ou.imply.cond, simplify=None)
    
    Eq << Eq.p_quote_definition.lhs.this.bisect(Slice[-1:])
    
    Eq << algebra.cond.forall_exists.imply.forall_exists_et.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.subs, swap=True)
    
    Eq <<= Eq[-1] & Eq.exists_n_plausible
    
    Eq << Eq[-1].this.function.apply(algebra.exists.exists.imply.exists_et, simplify=None)
    
    Eq << Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.subs, swap=True)   
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=n, start=2)
    
    Eq << Eq[1].subs(Eq[0])

    
if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
