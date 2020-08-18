from sympy.core.symbol import Symbol
from sympy.utility import plausible, identity
from sympy.core.relational import Equality
from sympy import S
from sympy.matrices.expressions.matexpr import HConcatenate, VConcatenate, \
    Addition, Multiplication
from sympy.matrices.expressions.determinant import det


@plausible
def apply(a, b, c):
    assert VConcatenate(b, c, a).shape == (3, 3)
    assert VConcatenate(c, a, b).shape == (3, 3)
    assert VConcatenate(a, b, c).shape == (3, 3)
    
    return Equality(det(VConcatenate(b, c, a) + VConcatenate(c, a, b)), det(VConcatenate(a, b, c)) * 2)


from sympy.utility import check


@check
def prove(Eq):
    a = Symbol('a', shape=(3,), complex=True)
    b = Symbol('b', shape=(3,), complex=True)
    c = Symbol('c', shape=(3,), complex=True)
    
    Eq << apply(a, b, c)
    
    L = Symbol('L', shape=(3, 3), definition=Eq[0].lhs.arg)
    Eq << identity(L).definition
    
    Eq << Addition(3, 0, 1) @ Eq[-1]    
    Eq << Addition(3, 0, 2) @ Eq[-1]
    Eq << Multiplication(3, 0, S.One / 2) @ Eq[-1]
    
    Eq << Addition(3, 1, 0, -1) @ Eq[-1]
    Eq << Multiplication(3, 1, -1) @ Eq[-1]
    
    Eq << Addition(3, 2, 0, -1) @ Eq[-1]
    Eq << Multiplication(3, 2, -1) @ Eq[-1]
    
    Eq << Addition(3, 0, 1, -1) @ Eq[-1]    
    Eq << Addition(3, 0, 2, -1) @ Eq[-1]
    
    Eq << Eq[-1].det() * 2
    
    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    prove(__file__)
