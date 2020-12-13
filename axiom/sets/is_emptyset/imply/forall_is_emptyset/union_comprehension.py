from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.sets import Interval
from axiom import sets
from sympy import ForAll, UNION
from sympy import Symbol
# given: Union[i](x[i]) = {}
# x[i] = {}


@plausible
def apply(given):
    assert given.is_Equality
    x_union, emptyset = given.args
    if emptyset:
        tmp = emptyset
        emptyset = x_union
        x_union = tmp
        assert emptyset.is_EmptySet

    assert x_union.is_UNION
    return ForAll(Equality(x_union.function, emptyset), *x_union.limits)


from axiom.utility import check


@check
def prove(Eq):
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True, positive=True, given=True)
    x = Symbol.x(shape=(k + 1,), etype=dtype.integer, given=True)

    Eq << apply(Equality(UNION[i:0:k](x[i]), x[i].etype.emptySet))

    j = Symbol.j(domain=Interval(0, k, integer=True))
    
    Eq << Eq[-1].limits_subs(i, j)
    
    Eq.paradox = ~Eq[-1]

    Eq.positive = Eq.paradox.apply(sets.is_nonemptyset.imply.is_positive)

    Eq.union_empty = Eq[0].abs()

    Eq << Eq[0] - Eq.paradox.lhs

    Eq << Eq[-1].abs()

    Eq << sets.imply.equality.principle.addition.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.union_empty)

    Eq << Eq[-1].subs(Eq.positive)


if __name__ == '__main__':
    prove(__file__)

