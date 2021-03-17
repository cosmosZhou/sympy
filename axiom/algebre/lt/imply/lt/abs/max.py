from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, swap=False):
    lhs, M = axiom.is_StrictLessThan(given)
    substract = axiom.is_Abs(lhs)
    a, b = axiom.is_Substract(substract)
#     |a - b| < M
    if swap:
        a, b = b, a
    return StrictLessThan(abs(a), Max(abs(M + b), abs(M - b)))


@prove
def prove(Eq):
    M = Symbol.M(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(StrictLessThan(abs(a - b), M))
    
    Eq << algebre.lt.imply.lt.having.abs.apply(Eq[0]) + b
    
    Eq << algebre.imply.le.abs.single.apply(M + b)
    
    Eq << algebre.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << LessThan(abs(M + b), Eq[1].rhs, plausible=True)
    
    Eq.strict_less_than = algebre.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << algebre.lt.imply.lt.having.abs.apply(Eq[0], negate=True) - b

    Eq << algebre.imply.le.abs.single.apply(M - b)
    
    Eq << algebre.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << LessThan(abs(M - b), Eq[1].rhs, plausible=True)
    
    Eq << algebre.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])
    
    Eq << algebre.lt.lt.imply.lt.abs.apply(Eq.strict_less_than, Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

