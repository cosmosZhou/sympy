from sympy.core.relational import Equality, LessThan, Unequality, \
    StrictGreaterThan, GreaterThan
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles

# provided: |A| = 0
# A == {}


def apply(provided):
    assert provided.is_Equality
    A, B = provided.args
    if B != 0:
        A = B
    assert A.is_Abs
    A = A.arg

    return Equality(A, S.EmptySet,
                    equivalent=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    equality = Equality(abs(A), 0, evaluate=False)

    Eq << equality

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(discrete.sets.emptyset.strict_greater_than)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove(__file__)

