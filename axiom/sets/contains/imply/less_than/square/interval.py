from axiom.utility import prove, apply
from sympy.sets.contains import Contains
from sympy import Symbol
import axiom
from sympy.core.relational import LessThan
from sympy.functions.elementary.extremum import Max
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
    return LessThan(x * x, Max(m * m, M * M))




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    M = Symbol.M(real=True)
    Eq << apply(Contains(x, Interval(m, M)))
    
    Eq << Eq[0].split()
    
    Eq << algebre.greater_than.less_than.imply.less_than.square.apply(Eq[-2], Eq[-1])

if __name__ == '__main__':
    prove(__file__)

