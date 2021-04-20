from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


# given: A in B 
# => {A} subset B
@apply
def apply(given):
    x, interval = axiom.is_Contains(given)
    axiom.is_real_Interval(interval)
    assert not interval.left_open
    assert not interval.right_open
    
    m = interval.min()
    assert m.is_zero
    M = interval.max()
    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    M = Symbol.M(real=True)
    Eq << apply(Contains(x, Interval(0, M)))
    
    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq << algebra.is_nonnegative.le.imply.le.square.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    prove()

