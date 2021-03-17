from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


# given: A in B 
# => {A} subset B
@apply
def apply(given):
    x, interval = axiom.is_Contains(given)
    axiom.is_real_Interval(interval)
    assert not interval.left_open
    assert not interval.right_open
    
    m = interval.min()
    M = interval.max()
    return LessThan(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    M = Symbol.M(real=True)
    Eq << apply(Contains(x, Interval(m, M)))
    
    Eq << sets.contains.imply.et.interval.apply(Eq[0])
    
    Eq << algebre.et.imply.cond.apply(Eq[-1])
    
    Eq << algebre.ge.le.imply.le.square.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    prove(__file__)

