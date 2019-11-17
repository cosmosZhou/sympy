from sympy.core.relational import Equality, LessThan, Unequality
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset, Supset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# provided: A = B
# A >> B
def apply(provided):
    assert provided.is_Equality
    A, B = provided.args
    assert A.is_set and B.is_set
    return Subset(A, B,
                    given=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    equality = Equality(A, B, evaluate=False)

    Eq << equality

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    prove(__file__)

