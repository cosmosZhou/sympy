from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy import S

# provided: |A| = 0
# A == {}


@plausible
def apply(provided):
    assert provided.is_Equality
    A, B = provided.args
    if B != 0:
        A = B
    assert A.is_Abs
    A = A.arg

    return Equality(A, S.EmptySet,
                    equivalent=provided)


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

