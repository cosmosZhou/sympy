from util import *


@apply(simplify=None)
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Suffice(cond, given & cond, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Eq[-1].apply(algebra.suffice.given.ou)

    Eq << algebra.ou.given.et.apply(Eq[-1])

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()