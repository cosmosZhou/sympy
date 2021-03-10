from sympy import *
from axiom.utility import prove, apply

from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(boole):
    assert boole.is_Boole
    et = axiom.is_Boole(boole)
    eqs = axiom.is_And(et)
    
    return Equality(boole, Times(*(Boole(eq)for eq in eqs)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
     
    Eq << apply(Boole((x > y) & (a > b)))
    
    Eq << Eq[0].this.rhs.args[0].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.flatten, index=0)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    


if __name__ == '__main__':
    prove(__file__)

