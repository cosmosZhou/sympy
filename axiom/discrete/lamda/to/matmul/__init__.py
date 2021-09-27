from util import *


@apply
def apply(lamda):
    ((A, b), (k, *k_m)), *j_limit, (i, *i_n) = lamda.of(Lamda[Sum[Mul]])

    if b._has(i):
        A, b = b, A
        assert not b._has(i)

    A = Lamda(A, (k, *k_m), (i, *i_n)).simplify()

    if j_limit:
        b = Lamda(b, *j_limit, (k, *k_m)).simplify()
    else:
        b = Lamda(b, (k, *k_m)).simplify()


    rhs = A @ b

    return Equal(lamda, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete

    i, j, k = Symbol(integer=True)
    n, m, d = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, m), real=True)
    #b = Symbol.b(real=True, shape=(m,))
    #Eq << apply(Lamda[i:n](Sum[j:m](A[i, j] * b[j])))

    B = Symbol(real=True, shape=(m, d))
    Eq << apply(Lamda[j:d, i:n](Sum[k:m](A[i, k] * B[k, j])))
    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()

from . import swapn
