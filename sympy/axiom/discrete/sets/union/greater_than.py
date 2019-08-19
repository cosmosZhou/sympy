from sympy.core.relational import Equality, LessThan, GreaterThan
from sympy.utility import plausible, cout, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete


def apply(A, B):
    return GreaterThan(abs(Union(A, B)), abs(A),
                    plausible=plausible())


from sympy.utility import check, identity


@check
def prove():
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    cout << apply(A, B)

    cout << identity(Eq[-1].lhs.arg).rewrite(complement=0)

    cout << Eq[-1].abs()

    cout << Eq[-1].subs(Eq[-1].rhs.args[1], 0)


if __name__ == '__main__':
    prove()

