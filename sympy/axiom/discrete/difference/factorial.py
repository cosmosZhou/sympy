from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Sum
from sympy.core.symbol import Symbol, generate_free_symbol
from sympy.functions.special.gamma_functions import gamma
from sympy.core.function import Difference, Function
from sympy.tensor.indexed import IndexedBase
from sympy.core.numbers import oo
from sympy.axiom.discrete.combinatorics.binomial import Pascal


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
    cout << Eq[-1].left.separate(back=1)


if __name__ == '__main__':
    prove()

