from util import *


@apply
def apply(self):
    (x, A, S[x]), (S[x], S[1]) = self.of(Derivative[MatMul])
    assert x.shape
    return Equal(self, (A + A.T) @ x)


@prove
def prove(Eq):
    from axiom import discrete, calculus, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    A = Symbol(real=True, shape=(n, n))
    Eq << apply(Derivative[x](x @ A @ x))

    Eq << MatMul(*Eq[-1].lhs.find(MatMul).args[:2]).this.apply(discrete.matmul.to.lamda, var={'k', 'j'})

    Eq << Eq[-1] @ x

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[0].lhs.this.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(calculus.derivative.to.lamda)

    Eq << Eq[-1].this.rhs.find(Derivative).apply(calculus.derivative.to.sum)

    Eq << Eq[-1].this.rhs.find(Derivative).apply(calculus.derivative.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda.to.matmul)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda.to.matmul)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda.to.matmul)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.identity)

    Eq << Eq[-1].this.find(Add).apply(discrete.add.to.matmul)
    


if __name__ == '__main__':
    run()
# created on 2021-12-25
# updated on 2021-12-26