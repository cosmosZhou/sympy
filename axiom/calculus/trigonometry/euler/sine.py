from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, geometry, calculus, sets


@apply
def apply(sinx):
    i = S.ImaginaryUnit
    assert sinx.is_Sin
    x = sinx.arg
    return Equal(sinx, (E ** (i * x) - E ** (-i * x)) / (2 * i))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(sin(x))
    
    i = S.ImaginaryUnit
    Eq << calculus.trigonometry.euler.formula.apply(x)
    
    Eq << calculus.trigonometry.euler.formula.apply(-x)
    
    Eq << Eq[-2] - Eq[-1]
    
    Eq << Eq[-1] / (2 * i)
    
    Eq << Eq[-1].reversed
    
    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    prove()

