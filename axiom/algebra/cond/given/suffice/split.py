from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Suffice(cond, given), Suffice(cond.invert().simplify(), given)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()

