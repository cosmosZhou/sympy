from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Equivalent)
    return Infer(fn, fn1)


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Assuming(*Eq[1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()
# created on 2018-01-25
