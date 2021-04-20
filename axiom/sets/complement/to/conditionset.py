from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(complement):
    U, C = axiom.is_Complement(complement)
    n = C.variable
    cond = C.condition
    axiom.is_even(cond)
    base_set = C.base_set
    assert base_set.is_UniversalSet
    
    return Equal(complement, conditionset(n, (-1) ** n < 0, U))


@prove
def prove(Eq):
    U = Symbol.U(etype=dtype.integer, given=True)
    n = Symbol.n(integer=True, given=True)

    Eq << apply(Complement(U, conditionset(n, (-1) ** n > 0)))

    A = Symbol.A(Eq[0].lhs)
    B = Symbol.B(Eq[0].rhs)
    
    Eq.forall_contains_in_B = ForAll[n:A](Contains(n, B), plausible=True)

    Eq << Eq.forall_contains_in_B.this.limits[0][1].definition
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << algebra.forall.given.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].apply(sets.notcontains.given.ou.split.complement)
    
    Eq << ~Eq[-1]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1])
    
    Eq.forall_contains_in_A = ForAll[n:B](Contains(n, A), plausible=True)
    
    Eq << Eq.forall_contains_in_A.this.limits[0][1].definition
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << algebra.forall.given.ou.apply(Eq[-1])

    Eq << sets.forall_contains.forall_contains.imply.eq.apply(Eq.forall_contains_in_A, Eq.forall_contains_in_B)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].reversed

if __name__ == '__main__':
    prove()

