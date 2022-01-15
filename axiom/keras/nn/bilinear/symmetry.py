from util import *


@apply
def apply(x, y, given):
    assert given.is_Equal
    W_T, W = given.args
    assert W_T == W.T

    return Equal(x @ W @ y, y @ W @ x)


@prove
def prove(Eq):
    from axiom import keras
    n = Symbol(integer=True)
    x, y = Symbol(shape=(n,), real=True)
    W = Symbol(shape=(n, n), real=True)

    Eq << apply(x, y, Equal(W.T, W))

    Eq << keras.nn.bilinear.transpose.apply(x, y, W)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-01-04
