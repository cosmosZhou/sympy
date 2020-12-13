from axiom.utility import plausible
from sympy.sets.contains import Contains
from sympy import Symbol
import axiom
from sympy.core.relational import LessThan
from sympy.sets.sets import Interval
from axiom import algebre


# given: A in B 
# => {A} subset B
@plausible
def apply(given):
    x, interval = axiom.is_Contains(given)
    axiom.is_real_Interval(interval)
    assert not interval.left_open
    assert not interval.right_open
    
    m = interval.min()
    assert m.is_zero
    M = interval.max()
    return LessThan(x * x, M * M)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    M = Symbol.M(real=True)
    Eq << apply(Contains(x, Interval(0, M)))
    
    Eq << Eq[0].split()
    
    Eq << algebre.is_nonnegative.less_than.imply.less_than.square.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    prove(__file__)

