from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.contains import Subset


# given: A = B
# A >> B
@plausible
def apply(given):
    assert given.is_Equality
    A, B = given.args
    assert A.is_set and B.is_set
    return Subset(A, B, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    equality = Equality(A, B, evaluate=False)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    prove(__file__)

