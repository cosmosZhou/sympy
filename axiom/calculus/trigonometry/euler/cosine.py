from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, geometry, calculus, sets


@apply
def apply(cosx):
    i = S.ImaginaryUnit
    assert cosx.is_Cos
    x = cosx.arg
    return Equal(cosx, (E ** (i * x) + E ** (-i * x)) / 2)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(cos(x))
    
    i = S.ImaginaryUnit
    Eq << calculus.trigonometry.euler.formula.apply(x)
    
    Eq << calculus.trigonometry.euler.formula.apply(-x)
    
    Eq << Eq[-2] + Eq[-1]
    
    Eq << Eq[-1] / 2
    
    Eq << Eq[-1].reversed

if __name__ == '__main__':
    prove()

