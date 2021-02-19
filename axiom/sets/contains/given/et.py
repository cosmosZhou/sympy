from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(imply):
    assert imply.is_Contains
    x, interval = imply.args
    assert interval.is_Interval
    
    if interval.is_integer:
        assert x.is_integer
        
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
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True, integer=True)))
    
    Eq << Eq[-1].split()
    
    Eq << sets.strict_less_than.imply.contains.apply(Eq[-2], simplify=False)
    
    Eq << sets.greater_than.imply.contains.apply(Eq[-2], simplify=False)
    
    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    prove(__file__)

