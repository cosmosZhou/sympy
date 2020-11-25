from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality, Unequality
from axiom.utility import plausible
from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import Interval
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import Or
from sympy.concrete.expr_with_limits import UNION, ForAll, LAMBDA
from sympy.core.numbers import oo
from sympy.concrete.summations import Sum
from axiom import sets


@plausible
def apply(n, k, A=None):
    j = Symbol.j(domain=Interval(0, k, integer=True))
    if A is None:
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", definition=Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", definition=LAMBDA[i:k + 1](Piecewise(({n} | x[i], Equality(i, j)), (x[i], True))))
        A = Symbol.A(definition=LAMBDA[j](UNION[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))        
        
    return Equality(abs(UNION[j](A[j])), Sum[j](abs(A[j])))


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)

    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)
    s1_quote = Eq[1].lhs 

    Eq.s1_quote_definition = s1_quote.assertion()

    i = Eq[0].lhs.indices[0]
    
    x_tuple = Eq.s1_quote_definition.limits[0][0]

    Eq.x_abs_positive_s1, Eq.x_abs_sum_s1, Eq.x_union_s1 = Eq.s1_quote_definition.split()

    j = Symbol.j(domain=Interval(0, k, integer=True))

    x_quote = Eq[0].lhs.base

    Eq << Eq[0].union_comprehension((i, 0, k))

    x_quote_union = Eq[-1].subs(Eq.x_union_s1)
    Eq << x_quote_union

    Eq << Eq[0].abs()
    x_quote_abs = Eq[-1]
    
    Eq << Eq[-1].sum((i, 0, k))

    Eq << sets.imply.less_than.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.x_abs_sum_s1)

    Eq << x_quote_union.abs()
    x_quote_union_abs = Eq[-1]

    u = Eq[-1].lhs.arg
    Eq << sets.imply.less_than.union_comprehension.apply(u.function, *u.limits)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-4].subs(Eq[-1])
    SqueezeTheorem = Eq[-1]

    Eq << x_quote_abs.astype(Or)
    
    Eq << Eq[-1].subs(i, j)
    
    Eq << Eq[-2].forall((i, Unequality(i, j)))

    Eq << sets.imply.greater_than.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq[-1].subs(Eq.x_abs_positive_s1.limits_subs(i, j))

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-4].subs(Eq.x_abs_positive_s1)

    Eq << (Eq[-1] & Eq[-2])

    Eq << (x_quote_union & SqueezeTheorem & Eq[-1])

    Eq.x_quote_definition = Eq[0].reference((i, 0, k))

    Eq << Eq.x_union_s1.intersect({n})

    Eq.nonoverlapping_s1_quote = Eq[-1].apply(sets.is_emptyset.imply.forall_is_emptyset.intersect)

    Eq.xi_complement_n = Eq.nonoverlapping_s1_quote.apply(sets.is_emptyset.imply.equality.complement, reverse=True)

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
    
    Eq << Eq[-1].apply(sets.equality.imply.supset)

    Eq << Eq[-1].this.function.subs(Eq[-1].function.variable, Eq[-1].variable)

    Eq << Eq[-1].definition

    Eq << Eq[-1].subs(Eq.x_quote_definition)

    Eq << Eq[-1].this.function.astype(Or)

    Eq << Eq[-1].split()
    
    Eq << Eq[-1].split()[1].intersect({n})
    Eq << Eq[-1].subs(Eq.nonoverlapping_s1_quote)
    
    Eq << (Eq[-3] - n.set).limits_subs(j_quote, i)
    
    Eq << Eq[-1].subs(Eq.xi_complement_n.subs(i, j)).subs(Eq.xi_complement_n)
    
    _i = i.copy(domain=Interval(0, k, integer=True) - {j})
    Eq << Eq[-1].limits_subs(i, _i)
    
    Eq << Eq.x_union_s1.function.lhs.this.bisect({_i, j})
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << sets.imply.less_than.union_comprehension.apply(*Eq[-1].rhs.args)
    
    Eq << Eq[-2].abs().subs(Eq.x_union_s1).subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.x_abs_sum_s1)
    
    Eq << Eq[-1].subs(Eq.x_abs_positive_s1.subs(i, j))
    
#     assert len(Eq.plausibles_dict) == 4

    Eq << Eq.nonoverlapping.union_comprehension(Eq.nonoverlapping.limits[1])

    Eq << Eq[-1].this.function.lhs.as_two_terms()

    Eq << Eq.A_definition_simplified.subs(j, j_quote)

    Eq << Eq[-2].subs(Eq[-1].reversed, Eq.A_definition_simplified.reversed)
    
    Eq << sets.forall_equality.imply.equality.nonoverlapping.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.arg.limits_subs(j_quote, j)
    
    Eq << Eq[-1].this.rhs.limits_subs(j_quote, j)
    

if __name__ == '__main__':
    prove(__file__)

