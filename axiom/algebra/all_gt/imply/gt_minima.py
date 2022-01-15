from util import *


@apply
def apply(given):
    (fx, M), *limits = given.of(All[Greater])
    return Minima(fx, *limits) > M


@prove(provable=False)
def prove(Eq):
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](f(x) > M))


if __name__ == '__main__':
    run()
# created on 2019-12-01
