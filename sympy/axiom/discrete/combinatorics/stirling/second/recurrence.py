from sympy.core.symbol import Symbol, Wild, dtype
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Sum, Ref, Union

from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import FiniteSet, imageset, Interval
from sympy.sets.contains import Subset, Supset, Contains
from sympy.logic.boolalg import And, plausibles_dict
from sympy.functions.elementary.complexes import Abs
from sympy.core.basic import _aresame
from sympy.core.function import Function, Application
from sympy.functions.elementary.piecewise import Piecewise
from sympy.tensor.indexed import IndexedBase
from sympy.axiom import discrete
from sympy.sets.conditionset import ConditionSet
from sympy.concrete.expr_with_limits import UnionComprehension


def apply(n, k):
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    k = Symbol('k', integer=True, nonnegative=True)

    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(n, k)

    cout << Equality.by_definition_of(Eq[0].lhs)
    cout << Equality.by_definition_of(Eq[0].rhs.args[1])
    cout << Equality.by_definition_of(Eq[0].rhs.args[0].args[1])

    s1 = Symbol('s1', definition=Eq[1].rhs.arg)
    s1_quote = Symbol("s1'", definition=Eq[1].rhs.arg.limits[0][1])
    s2 = Symbol('s2', definition=Eq[2].rhs.arg)
    s2_quote = Symbol("s2'", definition=Eq[2].rhs.arg.limits[0][1])
    s3 = Symbol('s3', definition=Eq[3].rhs.arg)
    s3_quote = Symbol("s3'", definition=Eq[3].rhs.arg.limits[0][1])

    e = Symbol('e', dtype=dtype.integer.set)
    s2_ = imageset(e, Union(e, FiniteSet(FiniteSet(n))), s2)

    plausible0 = Subset(s2_, s1, plausible=True)
    cout << plausible0

    cout << Eq[-1].definition

    cout << Eq[-1].simplifier()

    cout << Equality.by_definition_of(s2)

    cout << Equality.by_definition_of(s1)

    cout << Eq[-2].split()

    i = Eq[-1].lhs.limits[0][0]

    x, *_ = Eq[-1].function.variables
    x = x.base

    cout << Equality.define(x[k], FiniteSet(n))
    cout << Eq[-1].union(Eq[-2])

    cout << Eq[-1].this.function.function.rewrite()

    cout << Eq[-1].split()

    cout << Eq[12].set

    cout << Eq[-1].union(Eq[-3])

    cout << Eq[-1].swap()

    cout << Eq[12].abs()

    cout << Eq[10] + Eq[-1]

    cout << Eq[-1].this.function.function.rewrite()

    cout << Eq[-1].split()

    cout << Eq[20].subs(1, 0)

    cout << Eq[9].this.function.rewrite()
    cout << Eq[-1].split()

    cout << (Eq[-1] & Eq[-3])

    cout << (Eq[19] & Eq[16] & Eq[-1] & Eq[23])

    cout << Eq[-1].this.function.rewrite(index=-1)

    cout << Eq[6].this.function.definition
    
    cout << Eq[-1].subs(Eq[-1].variables[0], Eq[-2].variables[0])

    assert len(plausibles_dict(Eq)) == 1

    cout << Equality.by_definition_of(s3)

    s4 = Symbol('s4', definition=s3.definition.limits[0][1])
    cout << Equality.by_definition_of(s4)

    x_tuple = Eq[-1].limits[0][0]
    cout << Eq[-1].split()
    assert len(plausibles_dict(Eq)) == 1

    j = Symbol('j', integer=True, domain=Interval(0, k))

    x_ = IndexedBase("x'", (k + 1,), dtype=dtype.integer,
                     definition=Ref[i](Piecewise((Union(x_tuple[i], FiniteSet(n)) , Equality(i, j)), (x_tuple[i], True))))

    x_quote_definition = Equality.by_definition_of(x_)
    cout << x_quote_definition

    s4_imageset = imageset(x_tuple, x_, s4)
    imageFunction, imageSymbol, _ = s3.definition.image_set()

    s4_imageset_imageset = imageset(imageSymbol, imageFunction, s4_imageset)

    plausible1 = Subset(s4_imageset_imageset, s1, plausible=True)
    cout << plausible1

    cout << Eq[-1].definition

    cout << Eq[-1].simplifier()
    
    plausible1_simplified = Eq[-1]

    cout << Equality.by_definition_of(s4_imageset)

    cout << Eq[-1].split()

    positiveRequirement = Eq[-3]
    
    cout << Union[i:0:k](x_quote_definition)

    x_quote_union = Eq[-1].subs(Eq[-2])
    cout << x_quote_union

    cout << x_quote_definition.abs()
    x_quote_abs = Eq[-1]
    
    cout << Sum[i:0:k](Eq[-1])

    cout << discrete.sets.union.inequality.apply(*Eq[-1].rhs.args[1].arg.args)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].subs(Eq[41])

    cout << x_quote_union.abs()

    u = Eq[-1].lhs.arg
    cout << discrete.sets.union.inequalities.apply(u.function, *u.limits)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].subs(Eq[-4])
    SqueezeTheorem = Eq[-1]
     
    cout << x_quote_abs.split()

    cout << discrete.sets.union.greater_than.apply(*Eq[-2].rhs.arg.args[::-1])

#     cout << Eq[-1].subs(Eq[43])
    cout << Eq[-1].subs(positiveRequirement)
    
    cout << Eq[-4].subs(Eq[-1])

#     cout << Eq[-4].subs(Eq[43])
    cout << Eq[-4].subs(positiveRequirement)

    cout << (Eq[-1] & Eq[-2])

    cout << (x_quote_union & SqueezeTheorem & Eq[-1])

# application of assumption of other statements should be disallowed!
    cout << Eq[-1].this.function.subs(var=x[0:k + 1])

    cout << plausible1_simplified.this.function.definition

    b, *_ = Eq[-1].variables

    cout << Eq[-1].subs(x[0:k + 1], b)

    _b, *_ = Eq[-3].variables
    cout << Eq[-1].subs(b, _b)

    assert len(plausibles_dict(Eq)) == 1

    cout << Ref[i](x_quote_definition)
    
    x_quote_ref = Eq[-1]

    cout << plausible1.subs(Eq[-1])

    A = IndexedBase("A", (k + 1,), dtype=dtype.integer.set.set, definition=Ref[j](Eq[-1].args[0]))

    cout << Equality.by_definition_of(A)
    
    A_definition = Eq[-1]

    cout << Eq[-2].subs(Eq[-1].reversed)

    cout << Union[j](Eq[-1])

    B = Symbol("B", dtype=dtype.integer.set.set, definition=plausible0.args[0])

    cout << Equality.by_definition_of(B)

    cout << plausible0.subs(Eq[-1].reversed)

    cout << Eq[-3].union(Eq[-1])

    cout << Supset(*Eq[-1].args, plausible=True)  # unproven

    cout << ConditionSet(e, Contains(FiniteSet(n), e), s1).assertion(condition=False)

    cout << Subset(Eq[-1].rhs.args[0], Eq[-2].lhs.args[0], plausible=True)  # unproven
    cout << Supset(Eq[-2].rhs.args[0], Eq[-3].lhs.args[0], plausible=True)  # unproven

    cout << Subset(Eq[-3].rhs.args[1], Eq[-4].lhs.args[1], plausible=True)  # unproven
    cout << Supset(Eq[-4].rhs.args[1], Eq[-5].lhs.args[1], plausible=True)

    cout << Eq[-1].simplifier()

    cout << Eq[-1].subs(A_definition)

    cout << Eq[-1].subs(x_quote_ref.reversed)

    cout << Eq[-1].definition

    cout << Eq[-1].simplifier()

    cout << Eq[-1].this.function.definition

    cout << Eq[38].simplifier()
    cout << Eq[-1].split()

    cout << Eq[-1].negated

    cout << Eq[-1].definition

    l, *_ = Eq[-2].exists.keys()
    cout << Eq[-1].rewrite(var=l)

    cout << x_quote_ref[j]

    cout << Eq[-1].intersect(Eq[-2].reversed)

    cout << discrete.sets.union.inclusion_exclusion_principle.apply(*Eq[-1].lhs.args)

    cout << Eq[-1].subs(Eq[-2])

    cout << Eq[-1].subs(1, 0)

    cout << Eq[-1].rewrite(var=i)

    * _, _i = Eq[-1].exists.keys()
    cout << x_quote_union.left.bisect(domain={_i, j})

    cout << discrete.sets.union.inequality.apply(*Eq[-1].lhs.args)

    cout << discrete.sets.union.inequalities.apply(*Eq[-2].lhs.args[1].args)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].subs(Eq[98])

    b, *_ = Eq[53].forall.keys()
    cout << Eq[53].rewrite(var=b)

    cout << Eq[-2].subs(Eq[-1])

    cout << SqueezeTheorem.rewrite(var=b)

    cout << Eq[-2].subs(Eq[-1])

    cout << (Eq[89] & plausible1_simplified)

    assert len(plausibles_dict(Eq)) == 5

    cout << Eq[80].subs(Eq[74])

    cout << Eq[-1].definition

    var, *_ = Eq[-1].forall.keys()
    cout << Eq[-1].rewrite(var=var)

    cout << Eq[-1].definition

    var, *_ = Eq[5].forall.keys()
    cout << Eq[5].rewrite(var=var)
    assert len(plausibles_dict(Eq)) == 4

    cout << Eq[79].subs(Eq[74])

    cout << Eq[-1].definition

    cout << Eq[-1].definition


if __name__ == '__main__':
    prove()
