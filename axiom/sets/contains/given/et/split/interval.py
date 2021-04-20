from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(imply):
    assert imply.is_Contains
    x, interval = imply.args
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
    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq << sets.lt.imply.contains.apply(Eq[-2], simplify=False)
    
    Eq << sets.ge.imply.contains.apply(Eq[-2], simplify=False)
    
    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    prove()

