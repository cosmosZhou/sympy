from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol, Boole
from sympy.functions.elementary.piecewise import Piecewise


@apply
def apply(given):
    return Equality(Boole(given), 1)




@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(Contains(e, s))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    

if __name__ == '__main__':
    prove(__file__)

