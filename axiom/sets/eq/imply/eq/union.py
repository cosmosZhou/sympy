from axiom.utility import prove, apply
from sympy import *
import axiom
# given : A & B = A | B => A = B


@apply
def apply(given, S):
    A, B = axiom.is_Equal(given)
    return Equal(A | S, B | S)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    S = Symbol.S(etype=dtype.integer)
    
    Eq << apply(Equal(A, B), S)
    
    Eq << Eq[-1].subs(Eq[0])

if __name__ == '__main__':
    prove()

