from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    if not n >= 0:
        print('warning, not proved!')

    if not k > 0:
        print('warning, not proved!')
    return Equal(self, n / k * Binomial(n - 1, k - 1))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply(binomial(n, k))

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[0], cond=Equal(n, 0))

    Eq << Eq[-2].this.apply(algebra.suffice.subs)

    Eq << Eq[-1].this.lhs.apply(algebra.is_nonzero.imply.is_positive)

    Eq << Eq[-1].apply(algebra.suffice.given.all)

    n_ = Symbol.n(integer=True, positive=True)
    Eq << algebra.all.given.cond.subs.apply(Eq[-1], Eq[-1].variable, n_)

    Eq << Eq[-1].this.lhs.apply(discrete.binomial.to.mul)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binomial.to.mul)

    Eq << Eq[-1].this.lhs.find(Factorial).apply(discrete.factorial.to.mul)

    Eq << Eq[-1].this.find(Pow, Factorial).apply(discrete.factorial.to.mul)


if __name__ == '__main__':
    run()
