from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, plausible, Product, identity
from sympy.core.relational import Equality
from sympy import axiom
from sympy.matrices.expressions.determinant import Determinant

from sympy.axiom import equality
from sympy.functions.elementary import miscellaneous
from sympy.matrices.expressions.matexpr import Shift


# r = Symbol('r')
# n = Symbol('n', integer=True, positive=True)
def apply(r, n):
    if not n >= 2:
        return None
    k = Symbol('k', integer=True)
    i = Symbol('i', integer=True)
    j = Symbol('j', domain=Interval(0, n, right_open=True, integer=True))

    A = Ref[i:n - 1, j]((j + 1) ** (i + 1))
    R = Ref[j](1 - r ** (j + 1))
# note : [A, B].T = (A.T, B.T)
# [R, A] = (R.T, A.T).T

    return Equality(Determinant([R, A]),
                    (1 - r) ** n * Product[k:1:n - 1](factorial(k)),
                    plausible=plausible())


from sympy.utility import check


def numeric_prove():
    import numpy as np
    from scipy.special.basic import comb
    n = 8
    E = np.eye(n, dtype=int)
    print(E)

    for k in range(n):
        for j in range(n - 1, k - 1, -1):
            if j > 0:
                E[:, j] -= E[:, j - 1]

    print(E)
    _E = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(n):
            _E[i][j] = (-1) ** (j - i) * comb(j + 1, i + 1)

    print(_E)

    assert (_E == E).all()

    A = np.zeros((n - 1, n), dtype=int)
    for i in range(n - 1):
        for j in range(n):
            A[i][j] = (j + 1) ** (i + 1)

    print(A)
    A_ = A @ E
    print(A_)


@check
def prove():
    r = Symbol('r')
    n = Symbol('n', domain=Interval(2, oo, integer=True))

    cout << apply(r, n)

    (i, *_), (j, *_) = Eq[0].lhs.arg.args[1].limits
    E = Ref[i:n, j]((-1) ** (j - i) * binomial(j + 1, i + 1))

    cout << identity(Eq[0].lhs.arg @ E).expand()

    (k, *_), *_ = Eq[-1].rhs.args[1].function.limits

    cout << equality.combinatorics.stirling.second.definition.apply(i + 1, j + 1)

    cout << Eq[-1] * factorial(j + 1)
    cout << Eq[-1].reversed

    cout << Eq[-1].left.simplifier()

    cout << identity(Eq[1].rhs.args[1].function).subs_limits(k, k - 1)

    cout << Eq[-1].right.simplifier()

    cout << Eq[-1].subs(Eq[-3])

    cout << Eq[1].subs(Eq[-1])

    cout << identity(Eq[-1].rhs.args[0].function).simplifier()

    cout << Eq[-1].right.subs_limits(k, k - 1)
    cout << Eq[-1].right.expand()

    cout << Eq[-1].right.args[1].simplifier()

    cout << equality.combinatorics.binomial.theorem.apply(r, -1, j + 1)

    cout << Eq[-1].right.expand()

    cout << Eq[-1].right.simplifier()

    cout << Eq[-4] + (Eq[-1] - Eq[-1].lhs)

    cout << Eq[-1].right.simplifier()

    cout << Eq[-1].right.args[2].simplifier()

    cout << equality.combinatorics.binomial.theorem.apply(1, -1, j + 1)

    cout << Eq[-1].right.expand()

    cout << Eq[-1].right.simplifier()

    cout << Eq[-4] - Eq[-1]

    cout << Eq[-1].right.simplifier()

    cout << Eq[9].right.subs(Eq[-1])

    cout << Shift(n, 0, n - 1) @ Eq[-1]

    cout << Eq[-1].det()

    cout << Eq[-1].right.simplifier()

    cout << Eq[-1] * (-1) ** (n - 1)

    cout << Eq[-1].right.powsimp()

    s = Eq[-1].rhs.args[1].limits[0][0]
    cout << Eq[-1].right.args[1].subs_limits(s, k - 1)


#     cout << Eq[-1].rhs.args
if __name__ == '__main__':
    prove()
