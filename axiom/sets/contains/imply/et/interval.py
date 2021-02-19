from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(given):
    assert given.is_Contains
    x, interval = given.args
    assert interval.is_Interval
    a, b = interval.args
    if interval.left_open:
        if interval.right_open:
            return And(x > a, x < b)
        else:
            return And(x > a, x <= b)
    else:
        if interval.right_open:
            return And(x >= a, x < b)
        else:
            return And(x >= a, x <= b)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b)))
    
    Eq << Eq[-1].split()
    
    Eq << sets.contains.imply.less_than.where.interval.apply(Eq[0])
    Eq << sets.contains.imply.greater_than.where.interval.apply(Eq[0])


if __name__ == '__main__':
    prove(__file__)

