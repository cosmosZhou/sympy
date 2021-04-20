from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


@apply(given=None)
def apply(given, B):
    x, A = axiom.is_Contains(given)
    
    return Equivalent(given, Or(Contains(x, A // B), Contains(x, A & B)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    Eq << apply(Contains(x, A), B)
    
    Eq << Eq[-1].this.rhs.simplify()

    
if __name__ == '__main__':
    prove()

