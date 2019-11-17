from sympy.core.symbol import Symbol
from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible, Eq

from sympy.utility import Sum
from axiom.discrete.combinatorics.binomial import Pascal


def apply(x, y, n=None):
    k = Symbol('k', integer=True)
    if n is None:
        n = Symbol('n', integer=True, nonnegative=True)
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)), plausible=plausible(), forall=n)
    elif n < 0:
        return None
    else:
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)), plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    x = Symbol('x', integer=True)
    y = Symbol('y', integer=True)
    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(x, y, n)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << (Eq[-2] * (x + y)).powsimp()

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.as_one_term()

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq[-1].this.rhs.function.powsimp()

    (k, *_), *_ = Eq[-1].this.rhs.limits
    Eq << Eq[-1].this.rhs.as_two_terms()

    Eq << Eq[-1].this.rhs.args[1].subs(k, k - 1)

    Eq << Eq[-1].subs(Pascal.apply(n + 1, k))

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[0].subs(n, 0)


if __name__ == '__main__':
    prove(__file__)

