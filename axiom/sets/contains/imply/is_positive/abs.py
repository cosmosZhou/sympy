from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
# given: x != y
# x not in {y}


@apply
def apply(given):
    x, RR = axiom.is_Contains(given)
    RR |= {0}
    
    assert RR.is_UniversalSet
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    x = Symbol.x(complex=True)
    Eq << apply(Contains(x, Reals // {0}))
    
    Eq << sets.contains.imply.ou.split.union.apply(Eq[0], simplify=False)
    
    Eq.is_negative = Sufficient(Eq[-1].args[0], Eq[1], plausible=True)
    
    Eq << Eq.is_negative.this.lhs.apply(sets.contains.imply.is_negative)
    
    Eq << Eq[-1].this.lhs.apply(algebra.is_negative.imply.is_nonzero)
    
    Eq << Eq[-1].this.lhs.apply(algebra.is_nonzero.imply.is_positive.abs)
    
    Eq.is_positive = Sufficient(Eq[2].args[1], Eq[1], plausible=True)
    
    Eq << Eq.is_positive.this.lhs.apply(sets.contains.imply.is_positive)
    
    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.imply.is_nonzero)
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.ou.apply(Eq.is_negative, Eq.is_positive)
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
        

if __name__ == '__main__':
    prove()

