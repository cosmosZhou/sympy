from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Necessary(given, cond), Necessary(given, cond.invert())


@prove
def prove(Eq):
    e = Symbol(integer=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()

