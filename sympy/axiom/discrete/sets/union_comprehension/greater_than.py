from sympy.core.relational import Equality, LessThan, GreaterThan
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete


def apply(A, B):
    return GreaterThan(abs(Union(A, B)), abs(A),
                    plausible=plausible())


from sympy.utility import check, identity


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    Eq << apply(A, B)

    Eq << identity(Eq[-1].lhs.arg).rewrite(complement=0)

    Eq << Eq[-1].abs()

    Eq << Eq[-1].subs(Eq[-1].rhs.args[1], 0)


if __name__ == '__main__':
    prove(__file__)

