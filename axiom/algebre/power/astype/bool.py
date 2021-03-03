from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    boole, two = axiom.is_Power(self)
    assert two == 2
    assert boole.is_Boole
    return Equality(self, boole)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Boole(x > y) ** 2)
    
    Eq << Eq[0].this.rhs.apply(algebre.bool.astype.power.square)


if __name__ == '__main__':
    prove(__file__)

