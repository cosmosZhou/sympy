from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.contains import Supset
from sympy import var

# given: A = B
# A >> B
@plausible
def apply(given):
    assert given.is_Equality
    A, B = given.args
    assert A.is_set and B.is_set
    return Supset(A, B, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B

    equality = Equality(A, B)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    prove(__file__)

