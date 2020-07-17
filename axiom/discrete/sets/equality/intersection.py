from sympy.core.relational import Equality, Unequality, StrictGreaterThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy.sets.contains import Contains
from axiom.discrete import sets
from sympy.functions.elementary.piecewise import Piecewise
from sympy.sets.sets import EmptySet

# given : e.set & s = a, |a| > 0 => e in s


@plausible
def apply(e, s):
    return Equality(s & e.set, Piecewise((e.set, Contains(e, s)), (EmptySet(), True)))


from sympy.utility import check


@check
def prove(Eq):
    s = Symbol('s', dtype=dtype.integer)
    e = Symbol('e', integer=True)
    
    Eq << apply(e, s)
    
    Eq << Eq[-1].this.rhs.simplify()    
    

if __name__ == '__main__':
    prove(__file__)

