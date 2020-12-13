from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol
from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool

@plausible
def apply(given):
    return Equality(bool(given.invert()), 0)


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(Contains(e, s))
    
    Eq << Eq[-1].this.lhs.definition
    

if __name__ == '__main__':
    prove(__file__)

