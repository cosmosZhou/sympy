from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from axiom import sets
from sympy import Symbol, Slice
from sympy.concrete.expr_with_limits import UNION, LAMBDA, INTERSECTION, ForAll
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.sets.sets import Interval, CartesianSpace
from sympy.concrete.summations import Sum
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@plausible
def apply(A):
    n = A.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    d = Symbol.d(shape=(oo,), integer=True)
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    return Equality(Sum[k:1:n]((-1) ** (k + 1) * Sum[d[:k]:ForAll[j:i, i:k](d[j] < d[i]):CartesianSpace(Interval(0, n - 1, integer=True), k)](abs(INTERSECTION[i:k](A[d[i]])))),
                    abs(UNION[i:n](A[i])))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    A = Symbol.A(etype=dtype.integer, shape=(n,))
    
    Eq << apply(A)
    
    Eq << Eq[0].subs(n, 2)

    
if __name__ == '__main__':
    prove(__file__)

