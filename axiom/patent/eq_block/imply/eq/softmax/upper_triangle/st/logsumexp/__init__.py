from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n,  S[u]))), (A[i + n - u, i + n - u:], (S[i], S[0], S[u]))), (A[i, i:Min(n, i + u)], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[
                Sliced[Indexed, Tuple[Add]], 
                Tuple[Expr - Expr]
            ],
            Lamda[                                BlockMatrix[NegativeInfinity * OneMatrix]
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and u >= 2 and u <= n
    
    return Equal(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:n - u](BlockMatrix(ZeroMatrix(i), Exp(z[i]), ZeroMatrix(n - i - u))),
        Lamda[i:u](BlockMatrix(ZeroMatrix(n - u + i), Exp(z[i + n - u, :u - i])))))


@prove
def prove(Eq):
    from axiom import algebra, patent

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, u), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
        Lamda[i:n - u](A[i, i:i + u]),
        Lamda[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * OneMatrix(i)))) - Lamda[i:n](OneMatrix(u) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << algebra.eq.imply.eq.exp.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(Exp[Lamda[BlockMatrix]]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Lamda]]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(algebra.pow.to.mul.OneMatrix)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(algebra.lamda.to.pow)

    Eq << patent.eq_block.imply.eq.softmax.upper_triangle.st.exp.apply(Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-03
from . import tf
# updated on 2022-03-30
