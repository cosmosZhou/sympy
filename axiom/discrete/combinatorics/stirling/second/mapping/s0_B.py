from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import sets, algebre


@apply
def apply(n, k, s0=None, B=None):
    
    if s0 is None: 
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s0 = Symbol.s0(UNION[x[:k]:Stirling.conditionset(n, k, x)](x[:k].set_comprehension().set))
    if B is None:
        e = Symbol.e(**s0.etype.dict)
        assert e.is_extended_real
        B = Symbol.B(UNION[e:s0]({e | {n.set}}))
        
        assert B.definition.variable.is_extended_real        
    return Equality(abs(s0), abs(B))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    s0 = Eq[0].lhs
    
    s0_quote = Symbol.s_quote_0(conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))

    Eq << s0_quote.this.definition
    Eq.s0_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.function.arg, s0_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    e = Symbol.e(etype=dtype.integer.set)
    assert e.is_zero is None
    assert e.is_integer
    assert e.is_extended_real
    
    Eq << sets.imply.forall.baseset.apply(s0_quote)

    * _, Eq.x_union_s0 = algebre.forall_et.imply.forall.apply(Eq[-1])

    i = Symbol.i(integer=True)
    x = Eq[0].rhs.variable.base

    j = Symbol.j(domain=[0, k], integer=True)

    B = Eq[1].lhs
    assert B.definition.variable.is_extended_real
    assert e.is_zero is None
    assert e.is_integer
    assert e.is_extended_real 

    Eq.plausible_notcontains = ForAll(NotContains({n}, e), (e, s0), plausible=True)

    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(Eq.s0_definition)

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.contains.imply.exists_contains.having.union_comprehension)
    
    Eq << algebre.forall.exists.imply.exists_et.apply(Eq.x_union_s0, Eq[-1].reversed, simplify=None)
    
    Eq << Eq[-1].this.function.apply(sets.eq.eq.imply.eq.union)
    
    Eq << Eq[-1].this().function.lhs.simplify()
    
    Eq << Eq[-1].subs(Eq.x_union_s0)

    Eq << Eq.plausible_notcontains.apply(sets.notcontains.imply.is_emptyset.intersection)

    Eq.forall_s0_equality = Eq[-1].apply(sets.is_emptyset.imply.eq.complement)

    x_hat = Symbol(r"\hat{x}", LAMBDA[i](Piecewise((x[i] - {n} , Equality(i, j)), (x[i], True))))

    Eq.x_hat_definition = x_hat.equality_defined()

    Eq << algebre.eq.imply.ou.two.apply(Eq.x_hat_definition)
    
    Eq << Eq[-1].forall((i, Unequality(i, j)))
        
    Eq.B_assertion = sets.imply.forall_exists_eq.having.imageset.apply(B)

    assert Eq.B_assertion.lhs.args[0].is_zero is None
    assert Eq.B_assertion.lhs.args[0].is_integer
    assert Eq.B_assertion.lhs.args[0].is_extended_real
    Eq << Eq.B_assertion.apply(sets.eq.imply.eq.complement, {n.set})

    assert Eq[-1].lhs.args[0].is_zero is None
    Eq.forall_B_contains = Eq[-1].subs(Eq.forall_s0_equality).limits_subs(Eq[-1].variable, Eq[-1].function.variable)

    Eq.forall_s0_contains = sets.imply.forall_contains.having.imageset.apply(B)
    
    Eq << Eq.B_assertion.apply(sets.eq.imply.eq.intersect, {n.set}).limits_subs(Eq.B_assertion.variable, Eq.B_assertion.function.variable)

    Eq.forall_B_equality = Eq[-1].apply(sets.eq.imply.eq.union, Eq[-1].variable)
     
    Eq << sets.forall_contains.forall_contains.forall_eq.forall_eq.imply.eq.apply(Eq.forall_s0_contains,
                                                                                              Eq.forall_B_contains,
                                                                                              Eq.forall_s0_equality,
                                                                                              Eq.forall_B_equality)


if __name__ == '__main__':
    
#     python run.py axiom.discrete.matrix.determinant.expansion_by_minors axiom.discrete.combinatorics.permutation.index.swap axiom.discrete.matrix.elementary.swap.concatenate axiom.discrete.combinatorics.stirling.second.nonoverlapping axiom.discrete.matrix.vandermonde.matmul_equal axiom.discrete.difference.definition axiom.keras.softmax.relative_position_representation axiom.discrete.combinatorics.stirling.second.recurrence axiom.calculus.trigonometry.cosine.theorem axiom.discrete.combinatorics.stirling.second.mapping.s0_B
# python run.py axiom.discrete.matrix.elementary.shift.left axiom.discrete.combinatorics.stirling.second.mapping.s2_B axiom.discrete.combinatorics.stirling.second.definition axiom.discrete.matrix.determinant.abc axiom.discrete.combinatorics.stirling.second.mapping.s0_B
    prove(__file__)

