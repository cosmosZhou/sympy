from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre
# given: A != {}
# |A| > 0


@apply
def apply(given):
    A = axiom.is_nonemptyset(given)
    return Unequality(abs(A), 0)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(Unequality(A, A.etype.emptySet))

    Eq << sets.is_nonemptyset.imply.exists_contains.voidlimit.apply(Eq[0], simplify=False)
    
    Eq << Eq[-1].apply(sets.contains.imply.eq.union)
    
    Eq.exists = Eq[-1].apply(algebre.eq.imply.eq.abs)
    
    Eq << sets.imply.eq.principle.addition.apply(A, Eq[-1].variable.set)
    
    Eq << Unequality(Eq[-1].rhs, 0, plausible=True)
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << Eq.exists.reversed + Eq[-1]
    
    
if __name__ == '__main__':
    prove(__file__)

