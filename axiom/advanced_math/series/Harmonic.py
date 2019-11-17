from sympy.core.symbol import Symbol
from sympy.core.numbers import oo
from sympy.utility import Sum, plausible
from sympy.core.relational import Equality

from sympy.series.limits import Limit
from sympy.functions.elementary.exponential import log
from sympy.concrete.expr_with_limits import Forall
from axiom import advanced_math
from sympy.sets.sets import Interval


def apply(n):
    k = Symbol('k', integer=True)
    return Equality(Limit(Sum[k:1:n](1 / k) / log(n + 1), n, oo), 1,
             plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, positive=True)
    Eq << apply(n)
    
    x = Symbol('x', real=True)
    x0 = Symbol('x0', real=True, positive=True)
    Eq.continuity = Equality(Limit(1 / x, x, x0, "+-"), 1 / x0, plausible=True)

    Eq << Eq.continuity.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Interval(*ab, integer=True))    

    Eq << Eq.continuity.forall(x0, k, k + 1)

    Eq << advanced_math.integral.mean_value_theorems.apply(Eq[-1])
    
    Eq << Eq[-1].summation((k, *ab))


if __name__ == '__main__':
    prove(__file__)

