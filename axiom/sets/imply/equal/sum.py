from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.sets import Union, Intersection
from sympy import Symbol
from axiom import sets
from sympy.concrete.summations import Sum
from sympy.functions.elementary.piecewise import Piecewise
from sympy import Boole
from sympy.sets.contains import Contains

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply(imply=True)
def apply(s, wrt=None):
    assert s.is_set
    if wrt is None:
        wrt = s.generate_free_symbol(**s.etype.dict)
    return Equality(Sum[wrt:s](Boole(Contains(wrt, s))), abs(s))


from axiom.utility import prove


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer.set * n)

    Eq << apply(S)

    Eq << Eq[-1].this.lhs.function.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs().function.simplify()


if __name__ == '__main__':
    prove(__file__)

