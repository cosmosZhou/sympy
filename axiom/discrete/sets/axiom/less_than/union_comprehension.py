from sympy.core.relational import LessThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from axiom import discrete
from sympy.concrete.expr_with_limits import UNION
from sympy.core.numbers import oo
from sympy import Symbol, Slice
from sympy.concrete.summations import Sum

@plausible
def apply(expr, *limits):
    return LessThan(abs(UNION(expr, *limits)), Sum(abs(expr), *limits).simplify())


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True)
    A = Symbol.A(shape=(oo,), dtype=dtype.integer)
    Eq << apply(A[k], (k, 0, n))

    Eq << Eq[0].subs(n, 1).doit(deep=True)

    Eq << discrete.sets.axiom.less_than.union.apply(*Eq[-1].lhs.arg.args)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.arg.bisect(Slice[-1:])

    Eq << discrete.sets.axiom.less_than.union.apply(*Eq[-1].lhs.arg.args)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[2].this.rhs.bisect(Slice[-1:])


if __name__ == '__main__':
    prove(__file__)

