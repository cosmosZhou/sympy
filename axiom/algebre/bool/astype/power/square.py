from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(boole):
    assert boole.is_Boole
    return Equality(boole, boole * boole)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Boole(x > y))
    
    b = Symbol.b(Eq[0].lhs)
    Eq << Or(Equality(b, 0), Equality(b, 1), plausible=True)
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << sets.imply.contains.bool.apply(Eq[0].lhs)
    
    Eq << sets.contains.imply.ou.having.finiteset.two.apply(Eq[-1])
    
    Eq << algebre.ou.imply.is_zero.apply(Eq[1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.base.definition


if __name__ == '__main__':
    prove(__file__)

