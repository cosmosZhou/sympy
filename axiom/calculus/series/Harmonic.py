from sympy.core.symbol import Symbol
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.series.limits import Limit
from sympy.functions.elementary.exponential import log
from sympy.sets.sets import Interval
import axiom
from sympy.concrete.summations import Sum


@plausible
def apply(n):
    k = Symbol('k', integer=True)
    return Equality(Limit(Sum[k:1:n](1 / k) / log(n + 1), n, oo), 1)


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

    Eq.mean_value_theorem = axiom.calculus.integral.mean_value_theorem.apply(Eq[-1])

    Eq << Eq[-1].limits_assertion()

    Eq << Eq[-1].inverse().split()

    Eq << (Eq.mean_value_theorem.subs(Eq[-1]), Eq.mean_value_theorem.subs(Eq[-2]))

    Eq << (Eq[-1].summation((k, 1, n - 1)), Eq[-2].summation((k, 1, n)))
    
    Eq << (Eq[-1].this.lhs.doit(), Eq[-2].this.lhs.doit().reversed)
    
    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.limits_subs(k, k - 1) + 1

    assert Eq[-3].lhs > 0    
    Eq << (Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs) 
    
    Eq << (Eq[-2].limit(n, oo), Eq[-1].limit(n, oo))
    
    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    prove(__file__)

