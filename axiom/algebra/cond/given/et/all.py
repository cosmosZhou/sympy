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
    given = given.split(wrt.domain_conditioned(cond))
    if given.is_And:
        lhs, rhs = given.of(And)
        return lhs, rhs
    return given


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol.e(real=True)
    f = Function.f(real=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << algebra.all.all.imply.all.limits_union.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

