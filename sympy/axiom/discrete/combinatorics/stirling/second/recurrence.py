from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Sum

from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import FiniteSet, imageset, Union
from sympy.sets.contains import Subset
from sympy.logic.boolalg import And


def apply(n, k):
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    k = Symbol('k', integer=True, nonnegative=True)
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(n, k)

    cout << Equality.by_definition_of(Eq[0].lhs)
    cout << Equality.by_definition_of(Eq[0].rhs.args[1])
    cout << Equality.by_definition_of(Eq[0].rhs.args[0].args[1])

    s1 = Symbol('s1', definition=Eq[1].rhs.arg)
    s2 = Symbol('s2', definition=Eq[2].rhs.arg)
    s3 = Symbol('s3', definition=Eq[3].rhs.arg)

    from sympy.core.symbol import dtype

    e = Symbol('e', dtype=dtype.integer.set)
    s2_ = imageset(e, Union(e, FiniteSet(FiniteSet(n))), s2)

    cout << Subset(s2_, s1, plausible=True)

    cout << Eq[-1].definition

    cout << Eq[-1].simplifier()

    cout << Equality.by_definition_of(s2)

    cout << Equality.by_definition_of(s1)

    cout << Eq[-2].split()

    x, *_ = Eq[-1].exists.keys()
    x = x.base

    cout << Equality.define(x[k], FiniteSet(n))
    cout << Eq[-1].union(Eq[-2])

    cout << Eq[-1].rewrite(exists=True)

    cout << Eq[-1].split()

    cout << Eq[12].set

    cout << Eq[-1].union(Eq[-2])

    cout << Eq[12].abs()

    cout << Eq[10] + Eq[-1]

    cout << Eq[-1].rewrite(exists=True)
    cout << Eq[-1].split()

    cout << Eq[18].subs(1, 0)

    cout << Eq[9].rewrite(exists=True)
    cout << Eq[-1].split()

    cout << (Eq[21] & Eq[9])


if __name__ == '__main__':
    prove()
