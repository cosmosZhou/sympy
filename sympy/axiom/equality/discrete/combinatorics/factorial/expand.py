from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq
from sympy.core.symbol import Symbol
from sympy.functions.special.gamma_functions import gamma


def apply(n):
    return Equality(factorial(n), n * factorial(n - 1),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(n)
    cout << Eq[0].rewrite(gamma).expand(func=True)


if __name__ == '__main__':
    prove()
