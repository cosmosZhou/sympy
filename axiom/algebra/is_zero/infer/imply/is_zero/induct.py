from util import *


@apply
def apply(f0, suffice, n=None):
    assert n.is_given == False

    f0.of(Equal[0])
    fn, fn1 = suffice.of(Infer)

    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, 0) == f0
    assert n.domain.min() == 0

    return fn


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True, given=False)
    f = Symbol(integer=True, shape=(oo,))
    Eq << apply(Equal(f[0], 0), Infer(Equal(f[n], 0), Equal(f[n + 1], 0)), n=n)

    g = Symbol(Lamda[n](KroneckerDelta(f[n], 0)))

    Eq << g[0].this.definition

    Eq << Eq[-1].this.rhs.subs(Eq[0])

    Eq.is_nonzero = algebra.eq.imply.ne_zero.apply(Eq[-1])

    Eq.suffice = Infer(Unequal(g[n], 0), Unequal(g[n + 1], 0), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.reversed

    Eq << algebra.ne_zero.infer.imply.ne_zero.induct.apply(Eq.is_nonzero, Eq.suffice, n=n)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-04-17
