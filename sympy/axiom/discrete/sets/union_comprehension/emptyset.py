from sympy.core.relational import Equality, LessThan, Unequality, \
    StrictGreaterThan, GreaterThan
from sympy.utility import plausible, Sum, Union, identity
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Interval
from sympy.axiom import discrete
from sympy import S
from sympy.concrete.expr_with_limits import Exists, Forall
from sympy.logic.boolalg import plausibles, And
from sympy.tensor.indexed import IndexedBase
from sympy.axiom.discrete.sets.union import inclusion_exclusion_principle
from sympy.axiom.discrete.sets.emptyset import strict_greater_than

# provided: Union[i](x[i]) = {}
# x[i] = {}


def apply(provided):
    assert provided.is_Equality
    x_union, emptyset = provided.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = x_union
        x_union = tmp
        assert emptyset == S.EmptySet

    assert x_union.is_UnionComprehension
    return Forall(Equality(x_union.function, S.EmptySet),
                  *x_union.limits,
                  equivalent=provided,
                  plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    i = Symbol('i', integer=True)
    k = Symbol('k', integer=True, positive=True)
    x = IndexedBase('x', shape=(k + 1,), dtype=dtype.integer)

    equality = Equality(Union[i:0:k](x[i]), S.EmptySet)

    Eq << equality

    Eq << apply(equality)

    Eq << ~Eq[-1]

    j = Symbol('j', domain=Interval(0, k, integer=True))
    Eq.paradox = Eq[-1].limits_subs(i, j)

    Eq.positive = Eq.paradox.apply(discrete.sets.emptyset.strict_greater_than)

    Eq.union_empty = Eq[0].abs()

    Eq << Eq[0] - Eq.paradox.lhs

    Eq << Eq[-1].abs()

    Eq << Eq[-2].lhs.assertion()

    Eq << Eq[-1].subs(Eq[-2], Eq.union_empty)

    Eq << Eq[-1].subs(Eq.positive)


if __name__ == '__main__':
    prove(__file__)

