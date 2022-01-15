from util import *


@apply
def apply(given, *, cond=None):
    p, q = given.of(Infer)

    return Infer(p & cond, q), Infer(p & cond.invert(), q)


@prove
def prove(Eq):
    f, g = Function(integer=True)
    x, y = Symbol(integer=True)
    Eq << apply(Infer(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()


from . import ou
# created on 2020-09-21
