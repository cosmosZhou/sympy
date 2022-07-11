from util import *


@apply
def apply(self):
    hi, (i, a, b) = self.of(Sum)
    first = hi._subs(i, a)
    last = hi._subs(i, b - 1)

    return Equal(self, (first + last) * (b - a) / 2)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    k, h = Symbol(complex=True)
    a, b, i = Symbol(integer=True)
    Eq << apply(Sum[i:a:b](k * i + h))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq.eq = Eq[-1].this.rhs.apply(algebra.mul.to.add, 2)

    Eq << discrete.binom.to.add.Pascal.apply(Binomial(i + 1, 2))

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=1)

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, a, b)).reversed

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.telescope)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq.eq.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2022-01-15
