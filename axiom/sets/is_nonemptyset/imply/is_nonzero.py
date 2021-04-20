from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
# given: A != {}
# |A| > 0


@apply
def apply(given):
    A = axiom.is_nonemptyset(given)
    return Unequal(abs(A), 0)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.is_nonemptyset.imply.exists_contains.apply(Eq[0], simplify=False)
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.eq.union)
    
    Eq.exists = Eq[-1].this.function.apply(algebra.eq.imply.eq.abs)
    
    Eq << sets.imply.eq.principle.addition.apply(A, Eq[-1].variable.set)
    
    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)
    
    Eq << algebra.eq.ne.imply.ne.transit.apply(Eq[-1], Eq[-2])
    
    Eq << Eq.exists.reversed
    
    Eq << algebra.cond.exists.imply.exists_et.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.ne.imply.ne.transit)
    
    
    
    
if __name__ == '__main__':
    prove()

