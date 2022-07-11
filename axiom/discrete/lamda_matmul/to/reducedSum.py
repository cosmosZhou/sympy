from util import *


@apply
def apply(self):
    (*Q, K), (i, S[0], k) = self.of(Lamda[MatMul])
    Q = MatMul(*Q)
    Q = Lamda[i:k](Q).simplify()
    K = Lamda[i:k](K).simplify()
    return Equal(self, ReducedSum(Q * K), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    i = Symbol(integer=True)
    n, d = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, n + 1))
    Q = Symbol(shape=(n, d), real=True)
    K = Symbol(shape=(n, d), real=True)
    Eq << apply(Lamda[i:k](Q[i] @ K[i]))

    i = Symbol(domain=Range(k))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.reducedSum)

    

    


if __name__ == '__main__':
    run()
# created on 2022-03-16
