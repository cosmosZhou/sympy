from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Suffice(cond, given), Suffice(cond.invert(), given)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= Eq[-2].apply(algebra.suffice.given.ou), Eq[-1].apply(algebra.suffice.given.ou)

    Eq <<= algebra.ou.given.cond.apply(Eq[-2], index=1), algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()

