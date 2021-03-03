from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(boole, n=None):
    assert boole.is_Boole
    assert n.is_integer
    assert n > 0
    return Equality(boole, boole ** n)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    n = Symbol.n(integer=True, positive=True, given=False)
     
    Eq << apply(Boole(x > y), n)
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq[0] * Boole(x > y)
    
    Eq << Eq[-1].this.lhs.apply(algebre.power.astype.bool)
    
    Eq << Eq[-1].this.rhs.powsimp()
    
    Eq << Eq.induct.induct()

    Eq << algebre.sufficient.imply.condition.induction.apply(Eq[-1], n=n, start=1)

if __name__ == '__main__':
    prove(__file__)

