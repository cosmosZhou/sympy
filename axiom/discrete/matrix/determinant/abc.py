from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Addition, Multiplication, Shift
from axiom import algebra, sets


@apply
def apply(A):
    n = A.shape[0]
    k = Symbol.k(integer=True)    
    return Equal(det(Sum[k:1:n]((Shift(n, 0, n - 1) ** k) @ A)), det(A) * (n - 1) * (-1) ** (n - 1))


@prove
def prove(Eq):
    n = 6
    A = Symbol.A(shape=(n, n), complex=True)
    
    Eq << apply(A)
    
    Eq << Symbol.L(Eq[0].lhs.arg).this.definition
    shift = Eq[-1].rhs.function.args[0].base
    
    Eq.L_definition = Eq[-1].this.rhs.doit()
    
    Eq << (shift @ A).this.expand()
    
#     Eq << Eq[-1].this.rhs.function.apply(algebra.piecewise.flatten, index=1)
    
#     Eq << Eq[-1].this.rhs.function.args[1].cond.args[0].apply(sets.contains.imply.contains.interval.substract, 1)
    
    Eq << Eq[-1].this.rhs.doit()
    
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

    Eq << Multiplication(n, 0, S.One / (n - 1)) @ Eq[-1]

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
    
    Eq << Eq[-1].apply(algebra.eq.imply.eq.det)
    
    Eq << Eq[-1] * (n - 1)
    
    Eq << -Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    prove()
