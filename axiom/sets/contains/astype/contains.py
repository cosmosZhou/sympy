from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply(given=None)
def apply(given):
    x, interval = axiom.is_Contains(given)
    interval.is_Interval
    return Equivalent(given, Contains(-x, -interval))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(Contains(x, Interval(a, b)))
    
    Eq << Sufficient(*Eq[0].args, plausible=True)
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[0].apply(sets.contains.given.contains.interval.negate)
    
    Eq << Necessary(*Eq[0].args, plausible=True)
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[1].apply(sets.contains.given.contains.interval.negate)

    Eq <<= Eq[3] & Eq[1]
    
if __name__ == '__main__':
    prove(__file__)

