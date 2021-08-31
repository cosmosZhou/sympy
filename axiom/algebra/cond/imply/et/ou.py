from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean

    return Or(cond, given), Or(cond.invert(), given)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(integer=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << algebra.ou.given.cond.apply(Eq[-2], index=1)

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()

