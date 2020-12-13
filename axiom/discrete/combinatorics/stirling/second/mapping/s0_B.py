from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality, Unequality
from axiom.utility import plausible
from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.contains import NotContains
from sympy.functions.elementary.piecewise import Piecewise
from axiom import sets, algebre
from sympy import UNION, ForAll, LAMBDA
from sympy.core.numbers import oo

@plausible
def apply(n, k, s0=None, B=None):
    
    if s0 is None:    
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s0 = Symbol.s0(definition=UNION[x[:k]:Stirling.conditionset(n, k, x)](x[:k].set_comprehension().set))
    if B is None:
        e = Symbol.e(**s0.etype.dict)
        assert e.is_extended_real
        B = Symbol.B(definition=UNION[e:s0]({e | {n.set}}))
        
        assert B.definition.variable.is_extended_real        
    return Equality(abs(s0), abs(B))


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    s0 = Eq[0].lhs
    
    s0_quote = Symbol.s_quote_0(definition=s0.definition.limits[0][1])

    Eq << s0_quote.this.definition
    Eq.s0_definition = Eq[0].subs(Eq[-1].reversed)

    e = Symbol.e(etype=dtype.integer.set)
    assert e.is_zero is None
    assert e.is_integer
    assert e.is_extended_real
    
    Eq << sets.imply.forall.given.baseset.apply(s0_quote)

    *_, Eq.x_union_s0 = Eq[-1].split()

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

    Eq << Eq[-1].definition

    Eq << Eq.x_union_s0.union(Eq[-1].reversed).this().function.lhs.simplify()
    
    Eq << Eq[-1].subs(Eq.x_union_s0)

    Eq << Eq.plausible_notcontains.apply(sets.notcontains.imply.is_emptyset)

    Eq.forall_s0_equality = Eq[-1].apply(sets.is_emptyset.imply.equality.complement)

    x_hat = Symbol(r"\hat{x}", shape=(oo,), etype=dtype.integer,
                     definition=LAMBDA[i](Piecewise((x[i] - {n} , Equality(i, j)), (x[i], True))))

    Eq.x_hat_definition = x_hat.equality_defined()

    Eq << algebre.equality.imply.ou.two.apply(Eq.x_hat_definition)
    
    Eq << Eq[-1].forall((i, Unequality(i, j)))
    
    Eq.B_assertion = B.assertion()

    assert Eq.B_assertion.lhs.args[0].is_zero is None
    assert Eq.B_assertion.lhs.args[0].is_integer
    assert Eq.B_assertion.lhs.args[0].is_extended_real
    Eq << Eq.B_assertion - {n.set}

    assert Eq[-1].lhs.args[0].is_zero is None
    Eq.forall_B_contains = Eq[-1].subs(Eq.forall_s0_equality).limits_subs(Eq[-1].variable, Eq[-1].function.variable)

    Eq.forall_s0_contains = B.assertion(reverse=True)
    
    Eq << Eq.B_assertion.intersect({n.set}).limits_subs(Eq.B_assertion.variable, Eq.B_assertion.function.variable)

    Eq.forall_B_equality = Eq[-1].union(Eq[-1].variable)
     
    Eq << sets.forall_contains.forall_contains.forall_equality.forall_equality.imply.equality.apply(Eq.forall_s0_contains,
                                                                                              Eq.forall_B_contains,
                                                                                              Eq.forall_s0_equality,
                                                                                              Eq.forall_B_equality)

if __name__ == '__main__':
    
#     python run.py axiom.discrete.matrix.determinant.expansion_by_minors axiom.discrete.combinatorics.permutation.index.swap axiom.discrete.matrix.elementary.swap.concatenate axiom.discrete.combinatorics.stirling.second.nonoverlapping axiom.discrete.matrix.vandermonde.matmul_equality axiom.discrete.difference.definition axiom.neuron.softmax.relative_position_representation axiom.discrete.combinatorics.stirling.second.recurrence axiom.calculus.trigonometry.cosine.theorem axiom.discrete.combinatorics.stirling.second.mapping.s0_B
# python run.py axiom.discrete.matrix.elementary.shift.left axiom.discrete.combinatorics.stirling.second.mapping.s2_B axiom.discrete.combinatorics.stirling.second.definition axiom.discrete.matrix.determinant.abc axiom.discrete.combinatorics.stirling.second.mapping.s0_B
    prove(__file__)

