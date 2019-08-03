from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Sum
from sympy.core.symbol import Symbol, generate_free_symbol
from sympy.functions.special.gamma_functions import gamma
from sympy.core.function import Difference, Function
from sympy.tensor.indexed import IndexedBase
from sympy.core.numbers import oo
from sympy.axiom.discrete.combinatorics.binomial import Pascal
from sympy.axiom import discrete
import sympy
from sympy.sets.sets import Interval


def apply(x, n):
    if not isinstance(x, Symbol):
        return
    return Equality(Difference(x ** n, x, n),
                    factorial(n),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    x = Symbol('x')
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(x, n)
    cout << Eq[0].subs(n, 0).doit()
    cout << Eq[0].subs(n, n + 1)
    cout << Eq[-1].left.bisect(back=1)

    cout << Eq[-1].left.expr.doit()
    cout << discrete.combinatorics.binomial.theorem.apply(x, 1, n + 1) - x ** (n + 1)

    cout << Eq[-1].right.args[1].bisect(back=1)

    cout << Eq[-3].subs(Eq[-1])

    cout << Eq[-1].left.as_Sum()

    cout << Eq[-1].left.bisect(back=1)

    cout << Eq[-1].subs(Eq[0])

    cout << discrete.combinatorics.factorial.expand.apply(n + 1)

    cout << Eq[-2].right.subs(Eq[-1])

#     cout << Eq[-1].left.function.args[1].bisect(back=1)
    k = Eq[-1].lhs.limits[0][0]
    k = Symbol(k.name, integer=True, domain=Interval(0, n, right_open=True))
    cout << Eq[0].subs(n, k)
    cout << Difference(Eq[-1], x, n - k)

    cout << Eq[-1].left.as_one_term()

    cout << Eq[-4].subs(Eq[-1])


if __name__ == '__main__':
    prove()

