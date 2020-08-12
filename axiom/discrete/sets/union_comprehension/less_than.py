from sympy.core.relational import LessThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy.concrete.expr_with_limits import UnionComprehension
from sympy.concrete import summations
from sympy.core.numbers import oo


@plausible
def apply(expr, *limits):
    return LessThan(abs(UnionComprehension(expr, *limits)),
                    summations.Sum(abs(expr), *limits).simplify())


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, positive=True)
    k = Symbol('k', integer=True)
    A = Symbol('A', shape=(oo,), dtype=dtype.integer)
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

