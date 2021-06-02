from util import *


@apply
def apply(given, old, new):
    from axiom.algebra.all.imply.ou import rewrite_as_Or
    assert new not in old.domain
    domain = old.domain_bounded
    assert domain is not None and new not in domain
    assert given._has(old)

    cond = given.forall((old,))
    old = old.unbounded
    assert old != new
    ou = rewrite_as_Or(cond)

    return ou._subs(old, new)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True, shape=(oo,))
    j = Symbol.j(integer=True)
    t = Symbol.t(domain=Range(0, n + 1))

    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(f(x, t) > g(t), t, y[j])

    Eq << Eq[0].forall((t,))

    t = Eq[-1].variable
    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], t, y[j])


if __name__ == '__main__':
    run()

