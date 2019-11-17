from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# given A & B = {} => A - B = A
def apply(provided, reverse=False):
    assert provided.is_Equality
    AB, emptyset = provided.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = AB
        AB = tmp

    assert AB.is_Intersection

    A, B = AB.args

    if reverse:
        return Equality(B - A, B,
                    equivalent=provided,
                    plausible=plausible())

    return Equality(A - B, A,
                    equivalent=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    provided = Equality(A & B, S.EmptySet)
    Eq << provided
    Eq << apply(provided)

    Eq << provided.union(A - B).reversed


if __name__ == '__main__':
    prove(__file__)

