from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Infer(cond, given), Infer(cond.invert(), given)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= Eq[-2].apply(algebra.infer.given.ou), Eq[-1].apply(algebra.infer.given.ou)

    Eq <<= algebra.ou.given.cond.apply(Eq[-2], index=1), algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()

# created on 2018-08-13
# updated on 2018-08-13
