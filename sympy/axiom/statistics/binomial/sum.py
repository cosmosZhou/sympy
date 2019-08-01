from sympy.utility import cout, Eq, plausible
from sympy.core.relational import Equality

from sympy.stats.rv import Density, RandomSymbol
from sympy import Symbol

from sympy.stats.drv import SingleDiscretePSpace
from sympy.stats.drv_types import BinomialDistribution, Binomial
from sympy.logic.boolalg import plausibles_dict


def apply(x0, x1):
    if not isinstance(x0, RandomSymbol) or not isinstance(x1, RandomSymbol):
        return None
    pspace0 = x0.pspace
    pspace1 = x1.pspace
    if not isinstance(pspace0, SingleDiscretePSpace) or not isinstance(pspace1, SingleDiscretePSpace):
        return None
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, BinomialDistribution) or not isinstance(distribution1, BinomialDistribution):
        return None
    if distribution0.p != distribution1.p:
        return None

    Y = Binomial('y', distribution0.n + distribution1.n, distribution0.p)
    y = Y.symbol

    return Equality(Density(x0 + x1)(y), Density(Y)(y).doit(), plausible=plausible())


from sympy.utility import check


@check
def prove():

    from sympy import Interval
    n0 = Symbol("n0", integer=True, positive=True)
    n1 = Symbol("n1", integer=True, positive=True)
    p = Symbol("p", domain=Interval(0, 1))

    x0 = Binomial('x0', n0, p)
    x1 = Binomial('x1', n1, p)

    cout << apply(x0, x1)

    cout << Equality.by_definition_of(Density(x0 + x1))

    cout << Eq[-1].right.function.args[3].doit()

    cout << Eq[-1].right.function.powsimp()

    cout << Eq[-1].subs(Eq[0])

    from sympy import axiom

    cout << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n0)
    cout << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n1)

    cout << Eq[-1] * Eq[-2]
    cout << Eq[-1].left.powsimp()
    cout << axiom.discrete.combinatorics.binomial.theorem.apply(p, 1, n0 + n1).subs(Eq[-1])

    cout << Eq[-1].left.as_multiple_limits()

    (k, *_), (l, *_) = Eq[-1].left.limits
    cout << Eq[-1].left.subs(k, k - l)

    cout << Eq[-1].left.as_separate_limits()

    cout << Eq[-1].as_two_terms()

    y = Eq[0].lhs.symbol
    cout << Eq[-1].subscript(y).subs(Eq[4])


if __name__ == '__main__':
    prove()
