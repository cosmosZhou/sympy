from sympy.core.relational import Equality, LessThan, Unequality, \
    StrictGreaterThan, GreaterThan
from sympy.utility import plausible, Eq, Sum, Union, identity
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Interval
from axiom import discrete
from sympy import S
from sympy.concrete.expr_with_limits import Exists, Forall
from sympy.logic.boolalg import plausibles, And
from sympy.tensor.indexed import IndexedBase
from axiom.discrete.sets.union import inclusion_exclusion_principle
from axiom.discrete.sets.emptyset import strict_greater_than

# provided: A & Union[i](x[i]) = {}
# A & x[i] = {}


def apply(provided):
    assert provided.is_Equality
    x_union_intersect_A, emptyset = provided.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = x_union_intersect_A
        x_union_intersect_A = tmp
        assert emptyset == S.EmptySet

    assert x_union_intersect_A.is_Intersection
    x_union, A = x_union_intersect_A.args

    if not x_union.is_UnionComprehension:
        tmp = x_union
        x_union = A
        A = tmp
    assert x_union.is_UnionComprehension

    return Forall(Equality(x_union.function & A, S.EmptySet),
                  *x_union.limits,
                  equivalent=provided,
                  plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    i = Symbol('i', integer=True)
    k = Symbol('k', integer=True, positive=True)
    x = IndexedBase('x', shape=(k + 1,), dtype=dtype.integer)

    equality = Equality(Union[i:0:k](x[i]) & A, S.EmptySet)

    Eq << equality

    Eq << apply(equality)

    Eq << identity(Union[i:0:k](x[i] & A)).simplifier()

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].apply(discrete.sets.union_comprehension.emptyset)


if __name__ == '__main__':
    prove(__file__)

