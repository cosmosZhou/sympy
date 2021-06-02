from util import *


# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(A):
    n = A.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    d = Symbol.d(shape=(oo,), integer=True)
    k = Symbol.k(domain=Range(0, n))
    return Equal(Sum[k:1:n + 1]((-1) ** (k + 1) * Sum[d[:k]:ForAll[j:i, i:k](d[j] < d[i]):CartesianSpace(Range(0, n), k)](abs(Cap[i:k](A[d[i]])))),
                    abs(Cup[i:n](A[i])))


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(domain=Range(2, oo))
    A = Symbol.A(etype=dtype.integer, shape=(n,))
    
    Eq << apply(A)
    
    Eq << Eq[0].subs(n, 2)

    
if __name__ == '__main__':
    run()

