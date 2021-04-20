from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(a, wrt=None):
    if wrt is None:
        wrt = a.generate_free_symbol(**a.type.dict)
    U = a.universalSet
    return Equal(conditionset(wrt, Unequal(wrt, a)), U // a.set)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))

    Eq << apply(x)
    
    A = Symbol.A(Eq[0].lhs)
    B = Symbol.B(Eq[0].rhs)
    
    a = Eq[0].lhs.variable
    Eq.forall_contains_in_B = ForAll[a:A](Contains(a, B), plausible=True)
    
    Eq << Eq.forall_contains_in_B.this.limits[0][1].definition
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq.forall_contains_in_A = ForAll[a:B](Contains(a, A), plausible=True)
    
    Eq << Eq.forall_contains_in_A.this.limits[0][1].definition
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << ForAll[a:Eq[-1].function.invert()](Eq[-1].limits_cond.invert(), plausible=True)
    
    Eq << Eq[-1].this.function.simplify()
    
    Eq << algebra.forall.imply.forall.limits.invert.apply(Eq[-1])

    Eq << sets.forall_contains.forall_contains.imply.eq.apply(Eq.forall_contains_in_A, Eq.forall_contains_in_B)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove()

