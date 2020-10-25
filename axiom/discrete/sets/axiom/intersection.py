from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise
from sympy.sets.sets import EmptySet
from sympy import Symbol
# given : e.set & s = a, |a| > 0 => e in s


@plausible
def apply(e, s):
    return Equality(s & e.set, Piecewise((e.set, Contains(e, s)), (EmptySet(), True)))


from axiom.utility import check


@check
def prove(Eq):
    s = Symbol.s(dtype=dtype.integer)
    e = Symbol.e(integer=True)
    
    Eq << apply(e, s)
    
    Eq << Eq[-1].this.rhs.simplify()    
    

if __name__ == '__main__':
    prove(__file__)

