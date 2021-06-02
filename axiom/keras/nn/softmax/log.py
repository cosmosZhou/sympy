from util import *


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(x):
    assert len(x.shape) == 1
    return Equal(log(softmax(x)), x - MAX(x) - log(ReducedSum(exp(x - MAX(x)))))


@prove
def prove(Eq):
    from axiom import keras, algebra
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(real=True, shape=(n,))
    Eq << apply(x)

    Eq << keras.nn.softmax.translation.apply(x, -MAX(x)).reversed

    Eq << Eq[-1].apply(algebra.eq.imply.eq.log)

    Eq << Eq[-1].this.rhs.arg.apply(keras.softmax.to.mul)


if __name__ == '__main__':
    run()
