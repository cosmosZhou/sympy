from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(imply):
    assert imply.is_Contains    
    
    e, interval = imply.args    
    
    return Contains(-e, -interval)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))

    Eq << sets.contains.imply.contains.interval.negate.apply(Eq[1])

    
if __name__ == '__main__':
    prove(__file__)

