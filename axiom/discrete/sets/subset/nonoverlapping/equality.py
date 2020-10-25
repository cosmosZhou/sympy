from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from axiom import discrete
from sympy import S
from sympy.sets.contains import Subset
from sympy import Symbol
# given0: A in B
# given1: B & C = {}
# C - A = C
@plausible
def apply(*given):
    assert len(given) == 2
    A = None
    B = None
    for p in given:
        if p.is_Subset:
            A, B = p.args
        elif p.is_Equality:
            BC, emptyset = p.args
            if emptyset != S.EmptySet:
                tmp = emptyset
                emptyset = BC
                BC = tmp
            assert BC.is_Intersection
            _B, C = BC.args
        else:
            return

    if B != _B:
        assert B == C
        C = _B

    return Equality(C - A, C, given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer, given=True)
    B = Symbol.B(dtype=dtype.integer, given=True)
    C = Symbol.C(dtype=dtype.integer, given=True)

    Eq << apply(Equality(B & C, S.EmptySet, evaluate=False), Subset(A, B, evaluate=False))

    Eq << discrete.sets.equality.emptyset.subset.apply(Eq[0], Eq[1])

    Eq << Eq[-1].union(Eq[-2].lhs).reversed


if __name__ == '__main__':
    prove(__file__)

