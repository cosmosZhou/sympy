from util import *


@apply(simplify=None)
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Infer(cond, given & cond, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Eq[-1].apply(algebra.infer.given.ou)

    Eq << algebra.ou.given.et.apply(Eq[-1])

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()
# created on 2018-08-30
