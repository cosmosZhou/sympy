from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from axiom import sets
from sympy import Symbol

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply(imply=True)
def apply(A, B):
    return Equality(abs(A | B), abs(A) + abs(B) - abs(A & B))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << sets.imply.equal.principle.addition.apply(B, A)
    
    Eq << Eq[-1].reversed + Eq[-2]
    
    Eq << Eq[-1] - Eq[-1].rhs.args[1]
    
    Eq << sets.imply.equal.principle.addition.apply(B - A, A & B).reversed


if __name__ == '__main__':
    prove(__file__)

