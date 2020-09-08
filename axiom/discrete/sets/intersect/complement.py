from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy import var

# given A & B = {} => A - B = A
@plausible
def apply(given, reverse=False):
    assert given.is_Equality
    AB, emptyset = given.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = AB
        AB = tmp

    assert AB.is_Intersection

    A, B = AB.args

    if reverse:
        return Equality(B - A, B, given=given)

    return Equality(A - B, A, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B

    Eq << apply(Equality(A & B, S.EmptySet))

    Eq << Eq[0].union(A - B).reversed


if __name__ == '__main__':
    prove(__file__)

