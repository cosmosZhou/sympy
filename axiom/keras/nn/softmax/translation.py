from util import *


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(x, delta):
    assert len(x.shape) == 1
    assert not delta.shape

    return Equal(softmax(x + delta), softmax(x))


@prove
def prove(Eq):
    from axiom import keras, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    delta = Symbol(real=True)
    Eq << apply(x, delta)

    Eq << Eq[-1].this.lhs.apply(keras.softmax.to.mul)

    Eq << Eq[-1].this.lhs.args[0].args[0].arg.apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Eq[-1].this.rhs.apply(keras.softmax.to.mul)


if __name__ == '__main__':
    run()
# created on 2021-01-05
