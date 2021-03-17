from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets


@apply(given=None)
def apply(given):
    x, interval = axiom.is_Contains(given)
    
    assert interval.is_Interval
    a, b = interval.start, interval.stop
    if interval.left_open:
        if interval.right_open:
            return Equivalent(given, And(x > a, x < b))
        else:
            return Equivalent(given, And(x > a, x <= b))
    else:
        if interval.right_open:
            return Equivalent(given, And(x >= a, x < b))
        else:
            return Equivalent(given, And(x >= a, x <= b))        


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(Contains(x, Interval(a, b)))

    Eq << Sufficient(*Eq[0].args, plausible=True)
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.et.interval, simplify=False)
    
    Eq << Necessary(*Eq[0].args, plausible=True)

    Eq << Eq[-1].this.rhs.apply(sets.le.ge.imply.contains)
    
    Eq <<= Eq[2] & Eq[1]

    
if __name__ == '__main__':
    prove(__file__)

