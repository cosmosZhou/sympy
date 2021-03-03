from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(complement, evaluate=True):
    union, C = axiom.is_Complement(complement)    
    union = axiom.is_Union(union)
    return Equality(complement, Union(*(u // C for u in union), evaluate=evaluate))


@prove
def prove(Eq):
    B = Symbol.B(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)

    Eq << apply((A | B) // C, evaluate=False)
    
    A = Symbol.A(A // C)
    B = Symbol.B(B // C)
    
    Eq.A_definition = A.this.definition
    Eq.B_definition = B.this.definition
    
    Eq << sets.equal.equal.imply.equal.union.apply(Eq.A_definition, Eq.B_definition)
    
    Eq << Eq[0].this.rhs.subs(Eq.A_definition.reversed, Eq.B_definition.reversed)
    
    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    prove(__file__)

