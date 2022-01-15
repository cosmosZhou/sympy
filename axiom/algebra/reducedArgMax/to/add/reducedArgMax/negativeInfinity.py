from util import *


@apply
def apply(self, k):
    x = self.of(ReducedArgMax)
    if k >= 0:
        ...
    else:
        assert k.copy(domain=self.domain_defined(k)) >= 0
    return Equal(self, ReducedArgMax(BlockMatrix[len(x.shape) - 1](-oo * OneMatrix(*x.shape[:-1], k), x)) - k)


@prove
def prove(Eq):
    from axiom import algebra

    k, n = Symbol(integer=True, positive=True)
    X = Symbol(real=True, shape=(n,), nonnegative=True)
    Eq << apply(ReducedArgMax(X), k)

    Eq << Eq[0].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)


if __name__ == '__main__':
    run()
# created on 2022-01-03
