from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.sets import Union, Intersection
from sympy import Symbol
from axiom import sets
from sympy.core.add import Plus
from sympy.functions.elementary.piecewise import Piecewise

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(given):
    assert given.is_Equality
    lhs, rhs = given.args
    if rhs.is_EmptySet:
        assert lhs.is_Intersection
        A, B = lhs.args
    else:
        assert lhs.is_EmptySet
        assert rhs.is_Intersection
        A, B = rhs.args

    return Equality(abs(Union(A, B)), abs(A) + abs(B))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equality(Intersection(A, B), A.etype.emptySet))
    
    Eq << sets.imply.eq.sum.apply(A | B).reversed
    
    Eq << sets.is_emptyset.imply.eq.bool.apply(Eq[0])
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.as_Plus = Eq[-1].this.rhs.astype(Plus)
    
    Eq <<= Eq.as_Plus.rhs.args[0].this.bisect(A), Eq.as_Plus.rhs.args[1].this.bisect(B)
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << Eq[-1] + Eq.as_Plus
    
    Eq << sets.imply.eq.sum.apply(A)
    
    Eq << sets.imply.eq.sum.apply(B)
    
    Eq << Eq[-1] + Eq[-2] + Eq[-3] 
    
   


if __name__ == '__main__':
    prove(__file__)

