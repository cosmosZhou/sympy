from sympy.core.relational import Equality, LessThan, Unequality
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# given A & B != emptyset
# then Exists[e:B] e in A
def apply(provided):
    assert provided.is_Unequality
    AB, emptyset = provided.args
    if emptyset != S.EmptySet:
        tmp = AB
        AB = emptyset
        emptyset = tmp
    assert AB.is_Intersection
    A, B = AB.args
    e = B.element_symbol(A.free_symbols)
    return Exists(Contains(e, A), (e, B),
                    equivalent=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    inequality = Unequality(A & B, S.EmptySet)
    Eq << inequality
    Eq << apply(inequality)

    Eq << (A & B).assertion()

    Eq << (Eq[-1] & inequality)

    Eq << Eq[-1].split()

    Eq << Eq[-1].split()

    Eq << (~Eq[1] & Eq[-2])


if __name__ == '__main__':
    prove(__file__)

