from sympy import *
from axiom.utility import prove, apply
import axiom
# given : A & B = A | B => A = B


@apply
def apply(given, S):
    A, B = axiom.is_Equal(given)
    return Equality(Complement(A, S), Complement(B, S))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    S = Symbol.S(etype=dtype.integer)
    
    Eq << apply(Equality(A, B), S)
    


if __name__ == '__main__':
    prove(__file__)

