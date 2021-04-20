from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


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
    
    Eq << algebra.equivalent.given.cond.apply(Eq[0])
    
    Eq <<= Eq[-2].apply(algebra.sufficient.given.ou), Eq[-1].apply(algebra.necessary.given.ou)
    
    Eq << Eq[-2].this.args[0].apply(sets.contains.given.contains.interval.negate)
    
    Eq << Eq[-1].this.args[1].apply(sets.contains.given.contains.interval.negate)
    
if __name__ == '__main__':
    prove()

