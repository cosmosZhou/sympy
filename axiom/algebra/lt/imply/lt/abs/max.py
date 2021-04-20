from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, swap=False):
    lhs, M = axiom.is_Less(given)
    substract = axiom.is_Abs(lhs)
    a, b = axiom.is_Substract(substract)
#     |a - b| < M
    if swap:
        a, b = b, a
    return Less(abs(a), Max(abs(M + b), abs(M - b)))


@prove
def prove(Eq):
    M = Symbol.M(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(Less(abs(a - b), M))
    
    Eq << algebra.lt.imply.lt.split.abs.apply(Eq[0]) + b
    
    Eq << algebra.imply.le.abs.apply(M + b)
    
    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << LessEqual(abs(M + b), Eq[1].rhs, plausible=True)
    
    Eq.strict_less_than = algebra.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << algebra.lt.imply.lt.split.abs.apply(Eq[0], negate=True) - b

    Eq << algebra.imply.le.abs.apply(M - b)
    
    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << LessEqual(abs(M - b), Eq[1].rhs, plausible=True)
    
    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << algebra.lt.lt.imply.lt.abs.apply(Eq.strict_less_than, Eq[-1])

    
if __name__ == '__main__':
    prove()

