from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol
from axiom import sets


# given A & B = {} => A - B = A
@apply(imply=True)
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




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equality(A & B, A.etype.emptySet))

    Eq << Eq[0].apply(sets.equal.imply.equal.union, A - B).reversed


if __name__ == '__main__':
    prove(__file__)

