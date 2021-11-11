from util import *


@apply
def apply(lamda):
    matmul, (j, *j_ab) = lamda.of(Lamda)
    if j_ab:
        a, b = j_ab
    else:
        a, b = matmul.domain_defined(j).of(Range)

    k = b - a
    assert a == 0

    A, B = matmul.of(MatMul)

    if A._has(j):
        assert not B._has(j)
        A = Lamda[j:k](A).simplify()
    else:
        assert B._has(j)
        i = B.generate_var(excludes=j, integer=True)
        n = B.shape[0]
        B = Lamda[j:k, i:n](B[i]).simplify()

    rhs = A @ B
    return Equal(lamda, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    j = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, m + 1))
    Q = Symbol(shape=(n,), real=True)
    K = Symbol(shape=(m, n), real=True)
    Eq << apply(Lamda[j:k](K[j] @ Q))

#     j = Symbol.j(integer=True)
#     n = Symbol.n(integer=True, positive=True)
#     m = Symbol.m(integer=True, positive=True)
#     k = Symbol.k(domain=Range(1, m + 1))
#     Q = Symbol.Q(shape=(n,), real=True)
#     K = Symbol.K(shape=(m, n), real=True)
#     Eq << apply(Lamda[j:k](Q @ K[j]))

    j = Symbol(domain=Range(k))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], j)


if __name__ == '__main__':
    run()

# created on 2020-08-17
# updated on 2020-08-17
