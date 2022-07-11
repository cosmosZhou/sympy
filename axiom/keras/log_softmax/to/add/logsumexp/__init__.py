from util import *


@apply
def apply(self):
    x = self.of(log[softmax])
    assert len(x.shape) == 1
    return Equal(self, x - logsumexp(x))


@prove
def prove(Eq):
    from axiom import keras, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(log(softmax(x)))

    Eq << Eq[0].find(softmax).this.apply(keras.softmax.to.mul.reducedSum)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.log)

    Eq << Eq[-1].this.rhs.apply(algebra.log.to.add)

    Eq << Eq[-1].this.find(Log[ReducedSum]).apply(keras.log_reducedSum.to.logsumexp)




if __name__ == '__main__':
    run()
# created on 2022-03-31


from . import max