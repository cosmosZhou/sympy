from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise
from sympy import Symbol
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(e, s):
    return Equality(s & e.set, Piecewise((e.set, Contains(e, s)), (e.emptySet, True)))




@prove
def prove(Eq):
    s = Symbol.s(etype=dtype.integer)
    e = Symbol.e(integer=True)
    
    Eq << apply(e, s)
    
    Eq << Eq[-1].this.rhs.simplify()    
    

if __name__ == '__main__':
    prove(__file__)

