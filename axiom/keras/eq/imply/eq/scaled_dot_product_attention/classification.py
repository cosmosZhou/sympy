from util import *


@apply
def apply(n, d, i):
    Q, K, V = Symbol(shape=(n, d), real=True)

    z = Symbol(softmax(Q @ K.T / sqrt(d)) @ V)

    return Equal(z[i], softmax(Q[i] @ K.T / sqrt(d)) @ V)


@prove
def prove(Eq):
    n, i = Symbol(integer=True)
    d = Symbol("d_z", integer=True)
    Eq << apply(n, d, i)

    M = Symbol(Eq[0].rhs.args[0].arg)
    Eq << M.this.definition

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1][i]

    Eq << Eq[2][i]

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-08-07
# updated on 2021-08-07
