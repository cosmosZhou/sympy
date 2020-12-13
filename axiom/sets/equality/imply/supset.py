from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Supset
from sympy import Symbol

# given: A = B
# A >> B
@plausible
def apply(given):
    assert given.is_Equality
    A, B = given.args
    assert A.is_set and B.is_set
    return Supset(A, B)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    equality = Equality(A, B)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    prove(__file__)

