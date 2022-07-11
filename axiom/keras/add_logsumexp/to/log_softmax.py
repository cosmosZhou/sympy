from util import *


@apply
def apply(self):
    x, S[x] = self.of(Expr - logsumexp)
    assert len(x.shape) == 1
    return Equal(self, log(softmax(x)))


@prove
def prove(Eq):
    from axiom import keras

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x - logsumexp(x))

    Eq << Eq[0].this.rhs.apply(keras.log_softmax.to.add.logsumexp)


if __name__ == '__main__':
    run()
# created on 2022-03-31
