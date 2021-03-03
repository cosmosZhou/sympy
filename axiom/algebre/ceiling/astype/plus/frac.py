from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre

@apply
def apply(self):
    x = axiom.is_Ceiling(self)

    return Equality(self, frac(-x) + x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(ceiling(x))
    
    Eq << Eq[0].this.rhs.args[1].definition
    
    Eq << Eq[-1].this.lhs.apply(algebre.ceiling.astype.times)

if __name__ == '__main__':
    prove(__file__)