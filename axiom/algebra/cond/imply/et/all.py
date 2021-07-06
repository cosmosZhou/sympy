from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    assert cond.is_boolean

    if wrt is None:
        wrt = cond.wrt
    if wrt.is_given:
        _eq = cond.invert()
        return Or(cond, given), Or(_eq, given)

    if wrt.is_bounded:
        from axiom.algebra.cond.imply.all import all
        given = all(given, wrt)
    else:
        given = All(given, (wrt,))
    assert given.is_All
    given = given.split(wrt.domain_conditioned(cond))
    lhs, rhs = given.of(And)
    return lhs, rhs


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= algebra.all.given.ou.apply(Eq[-2]), algebra.all.given.ou.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-2]

    


if __name__ == '__main__':
    run()

