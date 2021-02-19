from axiom.utility import prove, apply
from sympy.core.relational import Unequal, Equal
from sympy import Symbol
import axiom
from axiom import algebre
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.functions.elementary.piecewise import Piecewise


@apply
def apply(given):
    lhs, rhs = axiom.is_Unequal(given)
    return Equal(KroneckerDelta(lhs, rhs), 0)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(x, y))
    
    Eq << Eq[1].this.lhs.astype(Piecewise)    

if __name__ == '__main__':
    prove(__file__)
