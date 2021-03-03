from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self):
    div = axiom.is_Floor(self)
    plus, d = axiom.is_Divide(div)
    n = plus - (d - 1)

    return Equality(self, ceiling(n / d))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True, positive=True)
    Eq << apply(n // d)
    
    Eq << algebre.ceiling.astype.floor.apply(Eq[0].rhs).reversed
        
if __name__ == '__main__':
    prove(__file__)
