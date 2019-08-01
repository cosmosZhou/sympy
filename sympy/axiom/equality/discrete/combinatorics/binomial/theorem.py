from sympy.core.symbol import Symbol
from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq

from sympy.utility import Sum
from sympy.axiom.equality.discrete.combinatorics.binomial import Pascal

from sympy.logic.boolalg import plausibles_dict


def apply(x, y, n=None):
    k = Symbol('k', integer=True)
    if n is None:
        n = Symbol('n', integer=True, nonnegative=True)
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)), plausible=plausible(), for_clause=n)
    elif n < 0:
        return None
    else:
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)), plausible=plausible())


from sympy.utility import check


@check
def prove():
    x = Symbol('x', integer=True)
    y = Symbol('y', integer=True)
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(x, y, n)

    cout << Eq[-1].subs(n, n + 1)

    cout << (Eq[-2] * (x + y)).powsimp()

    cout << Eq[-1].subs(Eq[-2])

    cout << Eq[-1].right.as_one_term()

    cout << Eq[-1].right.function.expand()

    cout << Eq[-1].right.function.powsimp()

    (k, *_), *_ = Eq[-1].right.limits
    cout << Eq[-1].right.as_two_terms()

    cout << Eq[-1].right.args[1].subs(k, k - 1)

    cout << Eq[-1].subs(Pascal.apply(n + 1, k))

    cout << Eq[-1].left.expand()
    cout << Eq[-1].left.powsimp(deep=True)

    cout << Eq[-1].left.args[0].simplifier()

    cout << Eq[-1].left.simplifier()

    cout << Eq[0].subs(n, 0).right.doit()


if __name__ == '__main__':
    prove()

    print('plausibles_dict:')
    for index, eq in plausibles_dict(Eq).items():
        print("Eq[%d] : %s" % (index, eq))

# executive
# commander
