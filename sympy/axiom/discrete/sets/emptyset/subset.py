from sympy.core.relational import Equality, LessThan, Unequality
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset, Supset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# provided0: A in B
# provided1: B & C = {}
# and C & A = {}
def apply(*provided):
    assert len(provided) == 2
    A = None
    B = None
    for p in provided:
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

    return Equality(C & A, S.EmptySet,
                    given=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)
    C = Symbol('C', dtype=dtype.integer)

    subset = Subset(A, B, evaluate=False)

    equality = Equality(B & C, S.EmptySet, evaluate=False)

    Eq << equality

    Eq << subset

    Eq << apply(equality, subset)

    Eq << subset.intersect(C)

    Eq << Eq[-1].subs(equality)

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    prove(__file__)

