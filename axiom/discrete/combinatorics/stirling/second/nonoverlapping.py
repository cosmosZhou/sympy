from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import sets, algebre, discrete


@apply
def apply(n, k, A=None):
    assert k < n
    j = Symbol.j(domain=Interval(0, k, integer=True))
    if A is None:
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", definition=Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", definition=LAMBDA[i:k + 1](Piecewise(({n} | x[i], Equality(i, j)), (x[i], True))))
        A = Symbol.A(definition=LAMBDA[j](UNION[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))        
        
    return Equality(abs(UNION[j](A[j])), Sum[j](abs(A[j])))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(domain=Interval(1, n - 1, integer=True))
    
    Eq << apply(n, k)
    s1_quote = Eq[1].lhs 
    
    Eq.s1_quote_definition = sets.imply.forall.conditionset.apply(s1_quote)

    i = Eq[0].lhs.indices[0]
    
    Eq.x_abs_positive_s1, Eq.x_abs_sum_s1, Eq.x_union_s1 = Eq.s1_quote_definition.split()

    j = Symbol.j(domain=Interval(0, k, integer=True))

    Eq << sets.equal.imply.equal.union_comprehension.apply(Eq[0], (i, 0, k + 1))

    Eq.x_quote_union = Eq[-1].subs(Eq.x_union_s1)

    Eq << Eq[0].apply(algebre.equal.imply.equal.abs)
    x_quote_abs = Eq[-1]
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.sum, (i, 0, k + 1))

    Eq << sets.imply.less_than.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.x_abs_sum_s1)

    Eq << Eq.x_quote_union.apply(algebre.equal.imply.equal.abs)    

    u = Eq[-1].lhs.arg
    Eq.SqueezeTheorem = sets.imply.less_than.union_comprehension.apply(u.function, *u.limits)

    Eq << algebre.equal.imply.ou.two.apply(x_quote_abs)

    Eq << Eq[-1].subs(i, j)
    
    Eq << algebre.condition.imply.forall.minify.apply(Eq[-2], (i, Unequality(i, j)))

    Eq << sets.imply.greater_than.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.function.apply(algebre.strict_greater_than.greater_than.imply.strict_greater_than.transit, Eq[-1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq[-1]

    Eq.x_quote_definition = algebre.equal.imply.equal.lamda.apply(Eq[0], (i, 0, k + 1))

    Eq << Eq.x_union_s1.apply(sets.equal.imply.equal.intersect, {n})    

    Eq.nonoverlapping_s1_quote = Eq[-1].apply(sets.is_emptyset.imply.forall_is_emptyset.intersect)

    Eq.xi_complement_n = Eq.nonoverlapping_s1_quote.apply(sets.is_emptyset.imply.equal.complement, reverse=True)

    A_quote = Symbol.A_quote(shape=(k + 1,), etype=dtype.integer.set.set, definition=LAMBDA[j](Eq[2].rhs.function))

    Eq.A_quote_definition = A_quote.this.definition

    Eq.A_definition_simplified = Eq[2].this.rhs.subs(Eq.A_quote_definition[j].reversed)

    j_quote = Symbol.j_quote(integer=True)

    Eq.nonoverlapping = ForAll(Equality(A_quote[j_quote] & A_quote[j], A_quote[j].etype.emptySet), *((j_quote, Interval(0, k, integer=True) - {j}),) + Eq.A_definition_simplified.rhs.limits, plausible=True)

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].apply(sets.is_nonemptyset.imply.exists_contains.overlapping, simplify=None)

    Eq << Eq[-1].subs(Eq.A_quote_definition[j])

    Eq << Eq[-1].subs(Eq.A_quote_definition[j_quote])
    
    Eq << Eq[-1].this.function.rhs.function.arg.definition
    
    Eq << Eq[-1].apply(sets.equal.imply.supset)
    
    Eq << Eq[-1].apply(sets.supset.imply.forall_supset.where.union_comprehension)

    Eq << Eq[-1].this.function.subs(Eq[-1].function.variable, Eq[-1].variable)

    Eq << Eq[-1].apply(sets.contains.imply.exists_contains.where.union_comprehension)
    
    Eq << Eq[-1].subs(Eq.x_quote_definition)

    Eq << Eq[-1].apply(algebre.equal.imply.ou.two)

    Eq << Eq[-1].split()
    
    Eq << algebre.exists_et.imply.exists.limits_delete.apply(Eq[-2])
    
    Eq << Eq[-2].split()[1].apply(sets.equal.imply.equal.intersect, {n})
    
    Eq << Eq[-1].subs(Eq.nonoverlapping_s1_quote)
    
    Eq << (Eq[-2] - n.set).limits_subs(j_quote, i)
    
    Eq << Eq[-1].subs(Eq.xi_complement_n.subs(i, j)).subs(Eq.xi_complement_n)
    
    _i = i.copy(domain=Interval(0, k, integer=True) - {j})
    Eq << Eq[-1].limits_subs(i, _i)
    
    Eq << Eq.x_union_s1.function.lhs.this.bisect({_i, j})
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << sets.imply.less_than.union_comprehension.apply(*Eq[-1].rhs.args)
    
    Eq << Eq[-2].apply(algebre.equal.imply.equal.abs)
    
    Eq << Eq[-1].subs(Eq.x_union_s1) + Eq[-2]
    
    Eq << Eq[-1] + Eq.x_abs_sum_s1
    
    Eq <<= Eq[-1] & Eq.x_abs_positive_s1.subs(i, j)
    
    Eq << discrete.combinatorics.permutation.is_nonemptyset.s1.apply(n, k=k + 1)
    
    Eq << Eq[-1].subs(Eq[1].reversed)
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << Eq.nonoverlapping.apply(sets.equal.imply.equal.union_comprehension, Eq.nonoverlapping.limits[1])    

    Eq << Eq[-1].this.function.lhs.astype(Intersection)

    Eq << Eq.A_definition_simplified.subs(j, j_quote)

    Eq << Eq[-2].subs(Eq[-1].reversed, Eq.A_definition_simplified.reversed)
    
    Eq << sets.forall_equal.imply.equal.nonoverlapping.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.arg.limits_subs(j_quote, j)
    
    Eq << Eq[-1].this.rhs.limits_subs(j_quote, j)
    

if __name__ == '__main__':
    prove(__file__)

