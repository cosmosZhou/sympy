from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given: |A| >= 1
# A != {}


@apply
def apply(*given):
    greater_than, _greater_than = given
    x, a = axiom.is_LessEqual(greater_than)
    y, b = axiom.is_GreaterEqual(_greater_than)

    integer = x.is_integer and y.is_integer and a.is_integer and b.is_integer
    return Subset(Interval(y, x, integer=integer), Interval(b, a, integer=integer))


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(y <= b, x >= a)
    
    Eq << sets.subset.given.forall_contains.apply(Eq[-1])
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].this.function.apply(sets.notcontains.imply.ou.split.interval)
    
    Eq << algebra.exists.imply.exists_et.single_variable.apply(Eq[-1], simplify=None)
    
    Eq << Eq[-1].this.function.args[1].apply(sets.contains.imply.et.split.interval)
    
    #if self implies a False proposition, then self must be False
    Eq << Eq[-1].this.function.apply(algebra.et.given.ou, simplify=False)
    
    Eq.exists_ax, Eq.exists_by = Exists(Eq[-1].function.args[0], *Eq[-1].limits, plausible=True), Exists(Eq[-1].function.args[1], *Eq[-1].limits, plausible=True)
    
    Eq <<= algebra.exists_et.imply.exists.limits_absorb.apply(Eq.exists_ax, index=1), algebra.exists_et.imply.exists.limits_absorb.apply(Eq.exists_by, index=2)
    
    Eq <<= Eq[-2].this.function.apply(algebra.lt.ge.imply.lt.transit), Eq[-1].this.function.apply(algebra.gt.le.imply.gt.transit)
    
    Eq <<= Eq[-2] & Eq[1], Eq[-1] & Eq[0]
    
    Eq << ~(~Eq.exists_ax & ~Eq.exists_by)


if __name__ == '__main__':
    prove()

