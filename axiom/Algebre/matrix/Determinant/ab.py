from sympy.core.symbol import Symbol
from sympy.utility import plausible, identity
from sympy.core.relational import Equality
from sympy import S
from sympy.matrices.expressions.matexpr import HConcatenate, VConcatenate, \
    Addition, Multiplication
from sympy.matrices.expressions.determinant import det, Determinant
from sympy.matrices.dense import Matrix


@plausible
def apply(a, b):
    A = Matrix(((a[0],) * 4,
               (a[0],) + (a[1],) * 3,
               (a[0], a[1]) + (a[2],) * 2,
               (a[0], a[1], a[2], a[3])))
    
    B = Matrix(((b[0], b[1], b[2], b[3]),
               (b[1],) * 2 + (b[2], b[3]),
               (b[2],) * 3 + (b[3],),
               (b[3],) * 4))
    
    return Equality(Determinant(A * B), a[0] * b[3] * (a[3] * b[2] - a[2] * b[3]) * (a[2] * b[1] - a[1] * b[2]) * (a[1] * b[0] - a[0] * b[1]))


from sympy.utility import check


@check
def prove(Eq):
    a = Symbol('a', shape=(4,), complex=True, zero=False)
    b = Symbol('b', shape=(4,), complex=True, zero=False)
    Eq << apply(a, b)
    
    L = Symbol('L', shape=(4, 4), definition=Eq[0].lhs.arg)
    Eq << identity(L).definition
    
    Eq << Eq[-1] @ Multiplication(4, 0, 1 / a[0])
    
    Eq << Eq[-1] @ Multiplication(4, 3, 1 / b[3])
    
    Eq << Eq[-1] @ Multiplication(4, 2, 1 / b[2])
    
    Eq << Multiplication(4, 3, b[2]) @ Eq[-1] 
    
    Eq << Eq[-1].det()


if __name__ == '__main__':
    prove(__file__)
