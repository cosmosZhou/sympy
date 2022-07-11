from util import *


@apply
def apply(A, u):
    n, S[n] = A.shape
    assert A.is_real
    assert n >= 2 and u >= 2 and u <= n
    i = Symbol(integer=True)
    return BlockMatrix(
            Lamda[i:n - u](A[i, i:i + u]),
            Lamda[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * OneMatrix(i)))) <= Lamda[i:n](OneMatrix(u) * logsumexp(A[i, i:Min(n, i + u)]))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    Eq << apply(A, u)

    Eq << algebra.le.given.all.le.apply(Eq[0])

    Eq << algebra.le.given.le_zero.apply(Eq[-1])

    Eq << algebra.le_piece.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.find(LessEqual).apply(algebra.le_zero.given.le)

    Eq << Eq[-1].this.find(LessEqual[Zero]).apply(algebra.le_zero.given.le)

    Eq << Eq[-1].this.find(LessEqual[BlockMatrix]).apply(algebra.block_le.given.et.le)

    Eq.ou = Eq[-1].this.find(LessEqual).apply(algebra.le.given.all.le)

    Eq <<= keras.imply.le.logsumexp.apply(Eq.ou.find(Sliced)), keras.imply.le.logsumexp.apply(Eq.ou.args[1].find(Sliced))

    Eq <<= Eq.ou.find(Less).this.apply(algebra.lt.imply.lt.transport, rhs=1), Eq.ou.find(GreaterEqual).this.apply(algebra.ge.imply.ge.transport, rhs=1)

    Eq <<= Eq[-1].this.rhs.apply(algebra.ge.imply.eq.min), Eq[-2].this.rhs.apply(algebra.lt.imply.eq.min)

    Eq <<= algebra.cond.infer.imply.infer.et.rhs.apply(Eq[-2], Eq[-6]), algebra.cond.infer.imply.infer.et.rhs.apply(Eq[-1], Eq[-5])

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True, index=1), Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True, index=1)

    Eq << algebra.infer.infer.imply.ou.apply(Eq[-2], Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-04-01
