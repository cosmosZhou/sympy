from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(boole):
    assert boole.is_Boole
    return Contains(boole, {0, 1})


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Boole(x > y))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    S = Symbol.S(Eq[1].rhs)
    
    Eq << Or(Contains(1, S) & (x > y), Contains(0, S) & (x <= y), plausible=True)
    
    Eq << Eq[-1].this.args[0].args[0].rhs.definition
    
    Eq << Eq[-1].this.args[0].args[0].rhs.definition
    
    Eq << sets.ou.imply.contains.two.apply(Eq[-2], wrt=S)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << algebre.piecewise.swap.front.apply(Eq[-1].lhs)
    
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

