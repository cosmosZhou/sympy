from util import *


@apply(given=None)
def apply(given, limit):
    fk, A = given.of(Subset)
    k, a, b = limit
    assert not A._has(k)
    return Infer(All[k:a:b](Subset(fk, A)), Subset(Cup[k:a:b](fk), A))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    f = Function(shape=(), etype=dtype.integer)
    A = Symbol(etype=dtype.integer)
    Eq << apply(Subset(f(k), A), (k, 0, n))

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[0], cond=Subset(f(n), A))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2018-04-19
