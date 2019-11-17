from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from axiom import discrete
from sympy.concrete.expr_with_limits import UnionComprehension
from sympy.concrete import summations
from sympy.tensor.indexed import IndexedBase


def apply(expr, *limits):
    return LessThan(abs(UnionComprehension(expr, *limits)),
                    summations.Sum(abs(expr), *limits).simplifier(),
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, positive=True)
    k = Symbol('k', integer=True)
    A = IndexedBase('A', shape=(n,), dtype=dtype.integer)
    Eq << apply(A[k], (k, 0, n))

    Eq << Eq[0].subs(n, 1).doit(deep=True)

    Eq << discrete.sets.union.inequality.apply(*Eq[-1].lhs.arg.args)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.arg.bisect(back=1)

    Eq << discrete.sets.union.inequality.apply(*Eq[-1].lhs.arg.args)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[2].this.rhs.bisect(back=1)


if __name__ == '__main__':
    prove(__file__)

