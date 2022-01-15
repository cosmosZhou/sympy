from util import *


@apply(given=None)
def apply(given, limit):
    fk, gk = given.of(Equal)
    k, a, b = limit

    return Infer(All[k:a:b](Equal(fk, gk)), Equal(Cap[k:a:b](fk), Cap[k:a:b](gk)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)
    Eq << apply(Equal(f(k), g(k)), (k, 0, n))

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[0], cond=Equal(f(n), g(n)))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Eq[-1].this.rhs.apply(sets.eq.eq.imply.eq.cap.push_back)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2021-01-10
