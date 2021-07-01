from util import *



@apply(given=None)
def apply(given, n):
    x, Ak = given.of(Contains)
    A, k = Ak.of(Indexed)

    return Suffice(All[k:n](Contains(x, A[k])), Contains(x, Cap[k:n](A[k])))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True, given=False)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    A = Symbol.A(shape=(oo,), etype=dtype.integer)
    Eq << apply(Contains(x, A[k]), n)

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[0], cond=Contains(x, A[n]))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

