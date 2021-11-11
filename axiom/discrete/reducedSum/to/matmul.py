from util import *


@apply
def apply(self):
    x, y = self.of(ReducedSum[Mul])

    assert len(x.shape) == len(y.shape) == 1
    rhs = x @ y

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    y, x = Symbol(shape=(n,), real=True)
    Eq << apply(ReducedSum(x * y))

    Eq << Eq[0].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-11-16
# updated on 2020-11-16
