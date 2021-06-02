from util import *


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(x, delta):
    assert len(x.shape) == 1
    assert not delta.shape

    return Equal(softmax(x + delta), softmax(x))


@prove
def prove(Eq):
    from axiom import keras
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(real=True, shape=(n,))
    delta = Symbol.delta(real=True)
    Eq << apply(x, delta)

    Eq << Eq[-1].this.lhs.apply(keras.softmax.to.mul)

    Eq << Eq[-1].this.lhs.args[0].args[0].arg.astype(Mul)

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Eq[-1].this.rhs.apply(keras.softmax.to.mul)


if __name__ == '__main__':
    run()
