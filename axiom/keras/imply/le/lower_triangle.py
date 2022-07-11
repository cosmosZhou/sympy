from util import *


@apply
def apply(A, l):
    n, S[n] = A.shape
    assert A.is_real
    assert n >= 2 and l >= 2 and l <= n
    i = Symbol(integer=True)
    return BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1])),
            Lamda[i:n - l](A[i + l, i + 1:i + l + 1])) <= Lamda[i:n](OneMatrix(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    Eq << apply(A, l)

    Eq << algebra.le.given.all.le.apply(Eq[0])

    Eq << algebra.le.given.le_zero.apply(Eq[-1])

    Eq << algebra.le_piece.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.find(LessEqual).apply(algebra.le_zero.given.le)

    Eq << Eq[-1].this.find(LessEqual[Zero]).apply(algebra.le_zero.given.le)

    Eq << Eq[-1].this.find(LessEqual[BlockMatrix]).apply(algebra.block_le.given.et.le)

    Eq.ou = Eq[-1].this.find(LessEqual).apply(algebra.le.given.all.le)

    Eq <<= keras.imply.le.logsumexp.apply(Eq.ou.find(Sliced)), keras.imply.le.logsumexp.apply(Eq.ou.args[1].find(Sliced))

    Eq <<= Eq.ou.find(Less).this.apply(keras.lt.imply.relu_is_zero), Eq.ou.find(GreaterEqual).this.apply(keras.ge.imply.eq.relu)

    Eq <<= algebra.cond.infer.imply.infer.et.rhs.apply(Eq[-2], Eq[-4]), algebra.cond.infer.imply.infer.et.rhs.apply(Eq[-1], Eq[-3])

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True, index=1), Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True, index=1)

    Eq << algebra.infer.infer.imply.ou.apply(Eq[-2], Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2022-04-01
