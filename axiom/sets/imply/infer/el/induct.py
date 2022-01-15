from util import *



@apply(given=None)
def apply(given, n):
    x, Ak = given.of(Element)
    A, k = Ak.of(Indexed)

    return Infer(All[k:n](Element(x, A[k])), Element(x, Cap[k:n](A[k])))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    x, k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)
    Eq << apply(Element(x, A[k]), n)

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[0], cond=Element(x, A[n]))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2021-01-09
