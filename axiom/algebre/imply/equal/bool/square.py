from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(imply=True)
def apply(boole):
    assert boole.is_Boole
    return Equality(boole * boole, boole)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Boole(x > y))
    
    b = Symbol.b(definition=Eq[0].rhs)
    Eq << Or(Equality(b, 0), Equality(b, 1), plausible=True)
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << sets.imply.contains.bool.apply(Eq[0].rhs)
    
    Eq << sets.contains.imply.ou.where.finiteset.two.apply(Eq[-1])
    
    Eq << algebre.ou.imply.is_zero.apply(Eq[1])
    
    Eq << Eq[-1].this.lhs.expand().reversed
    
    Eq << Eq[-1].this.lhs.base.definition
    
    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    prove(__file__)

