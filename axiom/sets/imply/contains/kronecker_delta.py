from sympy import Symbol, Boole, Or
from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise

from sympy.core.function import Function
from axiom import algebre, sets
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(imply=True)
def apply(boole):
    assert boole.is_KroneckerDelta
    return Contains(boole, {0, 1})


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << sets.imply.contains.bool.apply(Boole(Equality(x, y)))    
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)

if __name__ == '__main__':
    prove(__file__)

