from axiom.utility import plausible
from sympy import Symbol
from sympy.concrete.expr_with_limits import ForAll, Exists
from sympy.sets.sets import Interval
from sympy.core.relational import Equality


@plausible
def apply(self):
    assert self.is_ExprWithLimits    
    return ForAll(self.limits_condition, *self.limits)

from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    f = Exists[x: Interval(0, n)](Equality(x * 2, 1)) 

    Eq << apply(f)
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove(__file__)

