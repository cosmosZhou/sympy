from axiom.utility import prove, apply

from sympy import *
import axiom
from axiom import sets


@apply(imply=True)
def apply(given):
    assert given.is_Contains
    x, interval = given.args
    assert interval.is_Interval
    a, b = interval.args
    
    if interval.left_open:
        if interval.right_open:
            ...
        else:
            return GreaterThan(b, x)    
    else:
        return GreaterThan(x, a)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))
    
    Eq << sets.contains.imply.et.interval.apply(Eq[0]).split()

    
if __name__ == '__main__':
    prove(__file__)

