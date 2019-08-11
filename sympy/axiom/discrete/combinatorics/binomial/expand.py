from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq
from sympy.core.symbol import Symbol


def apply(n=None, k=None):
    forall = None
    if n is None:
        n = Symbol('n', integer=True)
        forall = n

    if k is None:
        k = Symbol('k', integer=True)
        if forall is None:
            forall = k
        else:
            forall = [n, k]

    return Equality(binomial(n, k), n / k * binomial(n - 1, k - 1),
                    plausible=plausible(),
                    forall=forall)


from sympy.utility import check


@check
def prove():
    cout << apply()
    cout << Eq[-1].combsimp()


if __name__ == '__main__':
    prove()
