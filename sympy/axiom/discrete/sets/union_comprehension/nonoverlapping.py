from sympy.core.relational import Equality, LessThan, Unequality, \
    StrictGreaterThan, GreaterThan
from sympy.utility import plausible, Eq, Sum, Union, identity
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Interval
from sympy.axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset
from sympy.concrete.expr_with_limits import Exists, Forall
from sympy.logic.boolalg import plausibles
from sympy.tensor.indexed import IndexedBase
from sympy.axiom import discrete

# provided: |Union x[i]| = Sum |x[i]|
# x[i] & x[j] = {}


def apply(provided):
    assert provided.is_Equality
    x_union_abs, x_abs_sum = provided.args
    if not x_union_abs.is_Abs:
        tmp = x_union_abs
        x_union_abs = x_abs_sum
        x_abs_sum = tmp
        assert x_union_abs.is_Abs

    x_union = x_union_abs.arg
    assert x_union.is_UnionComprehension
    assert x_abs_sum.is_Sum
    assert x_abs_sum.function.is_Abs
    assert x_abs_sum.function.arg == x_union.function
    limits_dict = x_union.limits_dict
    i, *_ = limits_dict.keys()
    xi = x_union.function
    kwargs = i._assumptions.copy()
    if 'domain' in kwargs:
        del kwargs['domain']

    j = xi.generate_free_symbol(**kwargs)
    xj = xi.subs(i, j)

    i_domain = limits_dict[i] or i.domain

    limits = [(j, i_domain - {i})] + [*x_union.limits]
    return Forall(Equality(xi & xj, S.EmptySet),
                  *limits,
                  equivalent=provided,
                  plausible=plausible()).simplifier()


from sympy.utility import check


@check
def prove(Eq):
    i = Symbol('i', integer=True)
    k = Symbol('k', integer=True, positive=True)
    x = IndexedBase('x', shape=(k + 1,), dtype=dtype.integer)

    Eq << Equality(abs(Union[i:0:k](x[i])), Sum[i:0:k](abs(x[i])))

    Eq << apply(Eq[0])

    j = Eq[-1].variables[0]

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(discrete.sets.emptyset.strict_greater_than)

    Eq << discrete.sets.union.inclusion_exclusion_principle.apply(x[i], x[j])

    Eq << Eq[-1].subs(Eq[-2])

    Eq.strict_greater_than = Eq[0] - Eq[-1]

    Eq << identity(Eq[0].lhs.arg).bisect(domain={i, j})

    Eq.union_less_than = discrete.sets.union_comprehension.inequality.apply(x[i], *Eq[-1].rhs.args[0].limits)

    Eq << discrete.sets.union.inequality.apply(*Eq[-1].rhs.args)

    Eq << Eq.strict_greater_than.subs(Eq[-1])

    Eq << Eq[-1].simplifier(deep=True)

    Eq << Eq[-1].subs(Eq.union_less_than)

    Eq << Eq[-1].simplifier(deep=True)


if __name__ == '__main__':
    prove(__file__)

