from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(given):
    assert given.is_Contains
    x, interval = given.args
    assert interval.is_Interval
    a, b = interval.args
    
    if interval.right_open:
        if interval.left_open:
            ...
        else:
            return LessThan(a, x)
    else:
        return LessThan(x, b)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))
    
    Eq << sets.contains.imply.et.interval.apply(Eq[0]).split()
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

