from axiom.utility import prove, apply
from sympy.sets.contains import Contains
from sympy import Symbol
import axiom
from sympy.core.relational import LessThan
from sympy.sets.sets import Interval
from axiom import algebre


# given: A in B 
# => {A} subset B
@apply(imply=True)
def apply(given):
    x, interval = axiom.is_Contains(given)
    axiom.is_real_Interval(interval)
    assert not interval.left_open
    assert not interval.right_open
    
    m = interval.min()    
    M = interval.max()
    assert M.is_zero
    return LessThan(x * x, m * m)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    Eq << apply(Contains(x, Interval(m, 0)))
    
    Eq << Eq[0].split()
    
    Eq << algebre.is_nonpositive.greater_than.imply.less_than.square.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    prove(__file__)

