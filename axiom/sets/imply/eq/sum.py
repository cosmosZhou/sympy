from sympy import *
from axiom.utility import prove, apply
from axiom import sets
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(s, wrt=None):
    assert s.is_set
    if wrt is None:
        wrt = s.generate_free_symbol(**s.etype.dict)
    return Equality(Sum[wrt:s](Boole(Contains(wrt, s))), abs(s))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer.set * n)

    Eq << apply(S)

    Eq << Eq[-1].this.lhs.function.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs().function.simplify()


if __name__ == '__main__':
    prove(__file__)

