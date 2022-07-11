from util import *


@apply
def apply(lt):
    i, l = lt.of(Less)
    return Equal(relu(i + 1 - l), 0)


@prove
def prove(Eq):
    from axiom import keras, algebra

    i, l = Symbol(integer=True)
    Eq << apply(i < l)

    Eq << Eq[1].this.lhs.apply(keras.relu.to.add.min)

    Eq << algebra.lt.imply.le.strengthen.plus.apply(Eq[0])

    Eq << algebra.le.imply.eq.min.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-04-01
