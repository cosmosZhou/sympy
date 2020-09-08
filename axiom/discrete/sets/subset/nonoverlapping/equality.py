from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy import S
from sympy.sets.contains import Subset
from sympy import var
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


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B
    C = var(dtype=dtype.integer).C

    subset = Subset(A, B, evaluate=False)

    equality = Equality(B & C, S.EmptySet, evaluate=False)

    Eq << apply(equality, subset)

    Eq << discrete.sets.emptyset.subset.apply(equality, subset)

    Eq << Eq[-1].union(Eq[-2].lhs).reversed


if __name__ == '__main__':
    prove(__file__)

