from util import *


@apply(given=None)
def apply(given, limit):
    fk, gk = given.of(Equal)
    k, a, b = limit

    return Suffice(All[k:a:b](Equal(fk, gk)), Equal(Cup[k:a:b](fk), Cup[k:a:b](gk)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)
    Eq << apply(Equal(f(k), g(k)), (k, 0, n))

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[0], cond=Equal(f(n), g(n)))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Eq[-1].this.rhs.apply(sets.eq.eq.imply.eq.cup.push_back)

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

