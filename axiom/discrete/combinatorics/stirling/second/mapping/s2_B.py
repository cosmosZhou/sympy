from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality, StrictGreaterThan
from axiom.utility import plausible
from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import image_set, Interval, Union
from sympy.sets.contains import Subset, Supset, Contains, NotContains
from sympy.functions.elementary.piecewise import Piecewise
from axiom import sets
from sympy.sets.conditionset import conditionset
from sympy.concrete.expr_with_limits import UNION, ForAll, LAMBDA
from sympy.core.numbers import oo
from sympy.logic.boolalg import Or

@plausible
def apply(n, k, s2=None, B=None):
    if s2 is None:    
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s2 = Symbol.s2(definition=UNION[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].set_comprehension().set))
    e = Symbol.e(**s2.etype.dict)
    
    if B is None:
        x = s2.definition.variable.base
        s0 = Symbol.s0(definition=UNION[x[:k]:Stirling.conditionset(n, k, x)](x[:k].set_comprehension().set))
        
        B = Symbol.B(definition=UNION[e:s0]({e | {n.set}}))       
    
    return Equality(conditionset(e, Contains({n}, e), s2), B)


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    s2 = Eq[0].lhs
    s2_quote = Symbol.s_quote_2(definition=Eq[0].rhs.limits[0][1])

    Eq << s2_quote.this.definition

    Eq.s2_definition = Eq[0].subs(Eq[-1].reversed)

    s0 = Eq[1].lhs    
    s0_quote = Symbol.s_quote_0(definition=Eq[1].rhs.limits[0][1])

    Eq << s0_quote.this.definition
    Eq << Eq[1].subs(Eq[-1].reversed)
    s0_definition = Eq[-1]

    e = Symbol.e(etype=dtype.integer.set)
    s0_ = image_set(Union(e, {n.set}), e, s0)

    plausible0 = Subset(s0_, s2, plausible=True)
    Eq << plausible0

    Eq << Eq[-1].definition

    Eq << Eq[-1].this.limits[0][1].subs(s0_definition)
    Eq << Eq[-1].subs(Eq.s2_definition)
    s0_plausible = Eq[-1]

    Eq.s2_quote_definition = s2_quote.assertion()
    Eq << s0_quote.assertion()

    Eq << Eq[-1].split()
    x_abs_positive = Eq[-3]
    x_abs_sum = Eq[-2]
    x_union_s0 = Eq[-1]

    i = Eq[-1].lhs.limits[0][0]
    x = Eq[-1].variable.base

    Eq << Equality.define(x[k], {n})
    x_k_definition = Eq[-1]

    Eq << Eq[-1].union(Eq[-2])
    x_union = Eq[-1]

    Eq << x_k_definition.set

    Eq << Eq[-1].union(x[:k].set_comprehension())

    Eq << s0_plausible.subs(Eq[-1].reversed)

    Eq << Eq[-1].definition.definition

    Eq << x_k_definition.abs()

    Eq << Eq[-1].subs(StrictGreaterThan(1, 0, plausible=True))    
    
    Eq << x_abs_sum + Eq[-2]

    Eq << (x_abs_positive & Eq[-2])

    Eq << (x_union & Eq[-1] & Eq[-2])

    j = Symbol.j(domain=Interval(0, k, integer=True))

    B = Eq[2].lhs 

    Eq << plausible0.subs(Eq[2].reversed)
   
    Eq << s2.this.bisect(conditionset(e, Contains({n}, e), s2))

    Eq.subset_B = Subset(Eq[-1].rhs.args[0], Eq[-2].lhs, plausible=True)  # unproven
    Eq.supset_B = Supset(Eq[-1].rhs.args[0], Eq[-2].lhs, plausible=True)  # unproven

    Eq << Eq.supset_B.subs(Eq[2])

    Eq << Eq[-1].definition.definition    

    Eq << Eq.subset_B.subs(Eq[2])

    Eq << Eq[-1].definition.definition

    Eq.subset_B_definition = Eq[-1] - {n.set}
        
    num_plausibles = len(Eq.plausibles_dict)

    Eq.plausible_notcontains = ForAll(NotContains({n}, e), (e, s0), plausible=True)

    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(s0_definition)

    Eq << ~Eq[-1]

    Eq << Eq[-1].definition

    Eq << x_union_s0.union(Eq[-1].reversed).this().function.lhs.simplify()
    
    Eq << Eq[-1].subs(x_union_s0)

    assert num_plausibles == len(Eq.plausibles_dict)

    Eq << Eq.plausible_notcontains.apply(sets.notcontains.imply.is_emptyset)

    Eq.s0_complement_n = Eq[-1].apply(sets.is_emptyset.imply.equality.complement)

    Eq << Eq.subset_B_definition.subs(Eq.s0_complement_n)

    s2_n = Symbol('s_{2, n}', definition=Eq[-1].limits[0][1])

    Eq.s2_n_definition = s2_n.this.definition

    Eq << s2_n.assertion()

    Eq << Eq[-1].subs(Eq.s2_definition).split()

    Eq.s2_n_assertion = Eq[-2].definition

    Eq << Eq[-1].subs(Eq.s2_n_assertion)

    Eq << Eq[-1].definition

    Eq.x_j_definition = Eq[-1].limits_subs(Eq[-1].variable, j).reversed

    Eq.x_abs_positive_s2, Eq.x_abs_sum_s2, Eq.x_union_s2 = Eq.s2_quote_definition.split()

    Eq << Eq.x_union_s2 - Eq.x_j_definition

    Eq << Eq[-1].this.function.lhs.args[0].bisect({j})

    x_tilde = Symbol(r"\tilde{x}", shape=(k,), etype=dtype.integer,
                     definition=LAMBDA[i:k](Piecewise((x[i], i < j), (x[i + 1], True))))

    Eq.x_tilde_definition = x_tilde.equality_defined()

    Eq << Eq.x_tilde_definition.union_comprehension((i, 0, k - 1))

    Eq << Eq[-1].this.rhs.args[1].limits_subs(i, i - 1)

    Eq.x_tilde_union = Eq[-1].subs(Eq[-3])

    Eq.x_tilde_abs = Eq.x_tilde_definition.abs()

    Eq << Eq.x_tilde_abs.sum((i, 0, k - 1))

    Eq << Eq[-1].this.rhs.args[0].limits_subs(i, i - 1)

    Eq.x_tilde_abs_sum = Eq[-1].subs(Eq.x_abs_sum_s2, Eq.x_j_definition.abs())

    Eq << Eq.x_tilde_abs.astype(Or)
    Eq << Eq[-1].forall((i, i < j))
    
    Eq << Eq[-2].forall((i, i >= j))
    
    Eq << Eq[-2].subs(Eq.x_abs_positive_s2)    

    Eq << Eq[-2].subs(Eq.x_abs_positive_s2.limits_subs(i, i + 1))

    Eq << (Eq[-1] & Eq[-2])

    Eq << (Eq[-1] & Eq.x_tilde_abs_sum & Eq.x_tilde_union)

    Eq << Eq[-1].func(Contains(x_tilde, s0_quote), *Eq[-1].limits, plausible=True)

    Eq << Eq[-1].definition
    Eq << Eq[-1].this.function.args[0].simplify()
    
    Eq.x_tilde_set_in_s0 = Eq[-3].func(Contains(UNION.construct_finite_set(x_tilde), s0), *Eq[-3].limits, plausible=True)

    Eq << Eq.x_tilde_set_in_s0.subs(s0_definition)

    Eq << Eq[-1].definition

    Eq << Eq.x_tilde_definition.set.union_comprehension((i, 0, k - 1))

    Eq << Eq[-1].subs(Eq.x_j_definition)

    Eq << Eq[-1].subs(Eq.s2_n_assertion.reversed)

    Eq << Eq.x_tilde_set_in_s0.subs(Eq[-1])

    Eq << Eq[-1].this.limits[0].subs(Eq.s2_n_definition)
    
    Eq.subset_B_plausible = Eq.subset_B_definition.union({n.set})
    Eq << sets.imply.forall.apply(Eq.subset_B_plausible, simplify=False)
        
    Eq << Eq[-1].definition.split()[1]    
    Eq << Eq[-1].apply(sets.contains.imply.equality.union)    
    Eq << Eq.subset_B_plausible.subs(Eq[-1])
    
    Eq << Eq.supset_B.subs(Eq.subset_B)


if __name__ == '__main__':
    prove(__file__)

