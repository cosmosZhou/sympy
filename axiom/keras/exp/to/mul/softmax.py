from util import *


@apply
def apply(self):
    x = self.of(Exp)
    return Equal(self, Softmax(x) * ReducedSum(exp(x)))


@prove
def prove(Eq):
    from axiom import keras

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    Eq << apply(exp(x))

    Eq << Eq[-1].this.find(Softmax).apply(keras.softmax.to.mul.reducedSum)









if __name__ == '__main__':
    run()
# created on 2021-12-14
