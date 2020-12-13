from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype

from sympy import Symbol


# given A & B = {} => A - B = A
@plausible
def apply(given, reverse=False):
    assert given.is_Equality
    AB, emptyset = given.args
    if emptyset:
        tmp = emptyset
        emptyset = AB
        AB = tmp

    assert AB.is_Intersection

    A, B = AB.args

    if reverse:
        return Equality(B - A, B)

    return Equality(A - B, A)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equality(A & B, A.etype.emptySet))

    Eq << Eq[0].union(A - B).reversed


if __name__ == '__main__':
    prove(__file__)

