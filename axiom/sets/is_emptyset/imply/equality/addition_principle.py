from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.sets import Union, Intersection
from sympy import Symbol
from axiom import sets
from sympy.concrete.summations import Sum
from sympy.functions.elementary.piecewise import Piecewise
from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool
from sympy.sets.contains import Contains
from sympy.core.add import Plus

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@plausible
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


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equality(Intersection(A, B), A.etype.emptySet))
    
    Eq << sets.imply.equality.sum.apply(A | B).reversed
    
    Eq << sets.is_emptyset.imply.equality.bool.apply(Eq[0])
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.as_Plus = Eq[-1].this.rhs.astype(Plus)
    
    Eq <<= Eq.as_Plus.rhs.args[0].this.bisect(A), Eq.as_Plus.rhs.args[1].this.bisect(B)
    
    Eq <<= sets.is_emptyset.imply.equality.complement.apply(Eq[0], reverse=True), sets.is_emptyset.imply.equality.complement.apply(Eq[0])
    
    Eq <<= Eq[-4].subs(Eq[-2]), Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq <<= Eq[-1] & Eq.as_Plus
        
    Eq << sets.imply.equality.sum.apply(A) + sets.imply.equality.sum.apply(B)
    
    Eq.summary = Eq[-1] + Eq[-2]
    
    Eq <<= Eq.summary.rhs.args[2].this.bisect(A), Eq.summary.rhs.args[-1].this.bisect(B)
    
    Eq <<= Eq[-2].subs(Eq[0]), Eq[-1].subs(Eq[0])
    
    Eq <<= Eq[-2].this.rhs().function.simplify(), Eq[-1].this.rhs().function.simplify()
    
    Eq <<= Eq[-2].this.rhs.args[1].definition, Eq[-1].this.rhs.args[1].definition
    
    Eq << Eq[-2] + Eq[-1]
    
    Eq << Eq.summary + Eq[-1]
    
   


if __name__ == '__main__':
    prove(__file__)

