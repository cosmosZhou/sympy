from sympy.core.relational import Equality, LessThan, Unequality, \
    StrictGreaterThan, GreaterThan
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles

# provided: A != {}
# |A| > 0


def apply(provided):
    assert provided.is_Unequality
    A, B = provided.args
    if B != S.EmptySet:
        assert A == S.EmptySet
        A = B

    return StrictGreaterThan(abs(A), 0,
                    equivalent=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    inequality = Unequality(A, S.EmptySet, evaluate=False)

    Eq << inequality

    Eq << apply(inequality)

    Eq << inequality.abs()

    Eq << GreaterThan(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(inequality)


if __name__ == '__main__':
    prove(__file__)

