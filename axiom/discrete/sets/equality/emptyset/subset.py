from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import S
from sympy.sets.contains import Subset, Supset
from sympy import Symbol

# given0: A in B
# given1: B & C = {}
# and C & A = {}
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

    return Equality(C & A, S.EmptySet, given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    B = Symbol.B(dtype=dtype.integer)
    C = Symbol.C(dtype=dtype.integer)

    subset = Subset(A, B, evaluate=False)
    equality = Equality(B & C, S.EmptySet, evaluate=False)

    Eq << apply(equality, subset)

    Eq << subset.intersect(C)

    Eq << Eq[-1].subs(equality)

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    prove(__file__)

