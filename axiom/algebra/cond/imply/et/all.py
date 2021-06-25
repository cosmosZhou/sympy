from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    assert cond.is_boolean

    if wrt is None:
        wrt = cond.wrt
    if wrt.is_given:
        _eq = cond.invert()
        return And(Or(cond, given), Or(_eq, given))

    if wrt.is_bounded:
        given = given.forall((wrt,), simplify=False)
    else:
        given = All(given, (wrt,))
    assert given.is_All
    return given.split(wrt.domain_conditioned(cond))


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Eq[-1].this.args[0].apply(algebra.all.given.ou)

    Eq << Eq[-1].this.args[1].apply(algebra.all.given.ou)

    Eq << algebra.et.given.ou.collect.apply(Eq[-1], cond=Eq[0])


if __name__ == '__main__':
    run()

