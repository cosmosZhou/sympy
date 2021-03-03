from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self):
    div = axiom.is_Ceiling(self)
    n, d = axiom.is_Divide(div)

    return Equality(self, (n - 1) // d + 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(ceiling(n / d))
    
    Eq << Eq[0].this.lhs.apply(algebre.ceiling.astype.floor)
    
    Eq << Eq[-1].this.lhs.apply(algebre.floor.astype.plus.quotient)
    
    
if __name__ == '__main__':
    prove(__file__)
