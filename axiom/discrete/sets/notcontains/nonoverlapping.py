from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy.sets.contains import NotContains


# given e not in S
@plausible
def apply(given):
    assert given.is_NotContains
    e, s = given.args
    return Equality(e.set & s, S.EmptySet, given=given)


from sympy.utility import check


@check
def prove(Eq):
    s = Symbol('s', dtype=dtype.integer)
    e = Symbol('e', integer=True)

    Eq << apply(NotContains(e, s))

    Eq << Eq[-1].lhs.assertion()

    Eq << Eq[-1].split()

    Eq << Eq[-1].split()

    Eq << Eq[-1].this.function.simplifier()

    Eq << Eq[-1].subs(Eq[-1].limits[0][0], e)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << (Eq[-1] & Eq[0])

    Eq << (Eq[2] & (~Eq[3])).split()


if __name__ == '__main__':
    prove(__file__)

