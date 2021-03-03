from sympy import *
from axiom.utility import prove, apply

from axiom import algebre, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(boole):
    assert boole.is_Boole
    return Equality(boole, Piecewise((1, boole.arg), (0, True)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Boole(x > y))
    
    Eq << Eq[0].this.lhs.astype(Piecewise)


if __name__ == '__main__':
    prove(__file__)

