from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S


@plausible
def apply(A, B, C):
#     return Equality(A | (B - C), (A - B) | (A & B & C) | (B - C))
    A = B
    return Equality(A - (B - C), (A - B) | (A & B & C))


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)
    C = Symbol('C', dtype=dtype.integer)

    Eq << apply(A, B, C)

if __name__ == '__main__':
    prove(__file__)

