from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    assert cond.is_boolean

    if wrt is None:
        wrt = cond.wrt

    assert not wrt.is_given

    if wrt.is_bounded:
        given = given.forall((wrt,), simplify=False)
    else:
        given = All(given, (wrt,))
    assert given.is_All

    domain = wrt.domain_conditioned(cond)
    if not domain.is_integer:
        domain = wrt.domain_conditioned(cond)
    return given.split(wrt.domain_conditioned(cond))


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(real=True)
    f = Function.f(real=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Eq[-1].apply(algebra.all.all.imply.all.limits_union)


if __name__ == '__main__':
    run()

