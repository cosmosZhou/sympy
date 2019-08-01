from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Sum
from sympy.core.symbol import Symbol
from sympy.functions.special.gamma_functions import gamma
from sympy.core.function import Difference, Function
from sympy.tensor.indexed import IndexedBase
from sympy.core.numbers import oo
from sympy.axiom.equality.discrete.combinatorics.binomial import Pascal


def apply(fx, x, n):
    k = Symbol('k', integer=True, nonnegative=True)
    return Equality(Difference(fx, x, n),
                    Sum[k:0:n]((-1) ** (n - k) * binomial(n, k) * fx.subs(x, x + k)),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    f = Function('f')
    x = Symbol('x')
    fx = f(x)
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(fx, x, n)

    cout << Eq[-1].subs(n, 1).doit()
    cout << Eq[-1].subs(n, n + 1)

    cout << Eq[-1].left.doit()

    cout << Eq[0].subs(x, x + 1) - Eq[0]

    cout << Eq[-1].subs(Eq[-2])

    k = Eq[0].rhs.limits[0][0]
    cout << Pascal.apply(n + 1, k)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].expand()

    cout << Eq[-1].left.args[0].simplifier()

    cout << Eq[-1].right.args[0].args[1].simplifier()

    cout << Eq[-1].left.subs_limits(k, k + 1)

    cout << Eq[-1].right.simplifier()

    cout << -Eq[-1]

    cout << Eq[-1].left.expand()

    cout << Eq[-1].left.simplifier()


if __name__ == '__main__':
    prove()

