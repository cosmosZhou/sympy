from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self):
    negativeOne, flr = axiom.is_Times(self, copy=True)
    assert negativeOne == -1
    x = axiom.is_Ceiling(flr)
    return Equality(self, floor(-x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(-ceiling(x))
    
    Eq << Eq[0].this.rhs.apply(algebre.floor.astype.times.ceiling)

    
if __name__ == '__main__':
    prove(__file__)
