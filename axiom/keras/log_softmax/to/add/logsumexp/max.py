from util import *


@apply
def apply(x):
    assert len(x.shape) == 1
    return Equal(log(softmax(x)), x - ReducedMax(x) - logsumexp(x - ReducedMax(x)))


@prove
def prove(Eq):
    from axiom import keras, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x)

    Eq << keras.nn.softmax.translation.apply(x, -ReducedMax(x)).reversed

    Eq << Eq[-1].apply(algebra.eq.imply.eq.log)

    Eq << Eq[-1].this.rhs.arg.apply(keras.softmax.to.mul.reducedSum)

    Eq << Eq[-1].this.find(Log[ReducedSum]).apply(keras.log_reducedSum.to.logsumexp)





if __name__ == '__main__':
    run()
# created on 2021-01-06
# updated on 2022-03-31
