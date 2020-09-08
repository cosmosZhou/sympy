from sympy.core.relational import GreaterThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy import var

@plausible
def apply(A, B):
    return GreaterThan(abs(Union(A, B)), abs(A))


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B

    Eq << apply(A, B)

    Eq << Eq[-1].lhs.arg.this.rewrite(complement=0)

    Eq << Eq[-1].abs()

    Eq << Eq[-1].subs(Eq[-1].rhs.args[1], 0)


if __name__ == '__main__':
    prove(__file__)

