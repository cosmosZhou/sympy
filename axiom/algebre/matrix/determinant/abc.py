from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy import S
from sympy.matrices.expressions.matexpr import Addition, Multiplication, Shift
from sympy.matrices.expressions.determinant import det
from sympy.concrete.summations import Sum
from sympy import var

@plausible
def apply(A):
    n = A.shape[0]
    k = var(integer=True).k    
    return Equality(det(Sum[k:1:n-1]((Shift(n, 0, n - 1) ** k) @ A)), det(A) * (n - 1) * (-1) ** (n - 1))


from sympy.utility import check


@check
def prove(Eq):
    n = 6
    A = Symbol('A', shape=(n, n), complex=True)
    
    Eq << apply(A)
    
    L = Symbol('L', shape=(n, n), definition=Eq[0].lhs.arg)
    Eq << L.this.definition
    shift = Eq[-1].rhs.function.args[0].base
    
    Eq.L_definition = Eq[-1].this.rhs.doit()
    
    Eq << (shift @ A).this.expand()
    Eq << Eq[-1].this.rhs.as_Concatenate()
    
    Eq << shift @ Eq[-1]    
    Eq << shift @ Eq[-1]
    Eq << shift @ Eq[-1]
    Eq << shift @ Eq[-1]
    
    Eq << Eq[-1] + Eq[-2] + Eq[-3] + Eq[-4] + Eq[-5]
    Eq << Eq.L_definition.subs(Eq[-1])

    Eq << Addition(n, 0, 1) @ Eq[-1]        
    Eq << Addition(n, 0, 2) @ Eq[-1]
    Eq << Addition(n, 0, 3) @ Eq[-1]
    Eq << Addition(n, 0, 4) @ Eq[-1]
    Eq << Addition(n, 0, 5) @ Eq[-1]

    Eq << Multiplication(n, 0, S.One / (n-1)) @ Eq[-1]

    Eq << Multiplication(n, 1, -1) @ (Addition(n, 1, 0, -1) @ Eq[-1])    
    Eq << Multiplication(n, 2, -1) @ (Addition(n, 2, 0, -1) @ Eq[-1])    
    Eq << Multiplication(n, 3, -1) @ (Addition(n, 3, 0, -1) @ Eq[-1])
    Eq << Multiplication(n, 4, -1) @ (Addition(n, 4, 0, -1) @ Eq[-1])
    Eq << Multiplication(n, 5, -1) @ (Addition(n, 5, 0, -1) @ Eq[-1])
    
    Eq << Addition(n, 0, 1, -1) @ Eq[-1]    
    Eq << Addition(n, 0, 2, -1) @ Eq[-1]
    Eq << Addition(n, 0, 3, -1) @ Eq[-1]
    Eq << Addition(n, 0, 4, -1) @ Eq[-1]
    Eq << Addition(n, 0, 5, -1) @ Eq[-1]
    
    Eq << Eq[-1].det() * (n - 1)
    Eq << -Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    prove(__file__)
