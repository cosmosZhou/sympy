from util import *


@apply
def apply(self, var=None, *, simplify=True):
    A, B = self.of(MatMul)
    assert len(A.shape) == 1
    assert len(B.shape) == 1
    res = ReducedSum(A * B)
    if simplify:
        res = res.simplify()
    return Equal(self, res, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n,), complex=True)
    Eq << apply(A @ B)

    Eq << Eq[0].this.rhs.apply(discrete.reducedSum.to.matmul)

    


if __name__ == '__main__':
    run()
# created on 2022-03-16
# updated on 2022-04-02
