from util import *


@apply
def apply(A):
    n = A.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    d = Symbol.d(shape=(oo,), integer=True)
    k = Symbol.k(domain=Range(0, n + 1))
    M = Symbol.M(Lamda[k](Piecewise((Sum[d[:k]:ForAll[j:i, i:k](d[j] < d[i]):CartesianSpace(Range(0, n), k)](abs(Cap[i:k](A[d[i]]))), k > 0),
                                                (abs(Cup[i:n](A[i])), True))))

    assert M.shape[0] == n + 1
    return Equal(Sum[k]((-1) ** k * M[k]), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(domain=Range(2, oo))
    A = Symbol.A(etype=dtype.integer, shape=(n,))

    Eq << apply(A)

    _k = Eq[-1].lhs.variable
    k = _k.unbounded
    Eq << Eq[-1].this.lhs.limits_subs(_k, k)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[-1].this.lhs.split({0})

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-1].this.rhs.astype(Sum)

    Eq << Eq[0].subs(_k, 0)

    Eq << Eq[-2].this.lhs.subs(Eq[-1]).reversed

    Eq << Eq[0].subs(_k, k)

    Eq << Eq[-2].this.lhs.subs(Eq[-1])

    Eq << sets.imply.eq.principle.inclusion_exclusion.deduction.apply(A)


if __name__ == '__main__':
    run()

from . import deduction
del basic
from . import basic

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml
