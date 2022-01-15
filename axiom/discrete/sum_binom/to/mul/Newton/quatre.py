from util import *


@apply
def apply(self):
    ((n, k), (S[k], S[4]), (x, S[k])), (S[k], a, S[n + 1]) = self.of(Sum[Binomial * Pow * Pow])
    assert a == 0 or a == 1
    return Equal(self, RisingFactorial(n * x, 4) * (x + 1) ** (n - 4) - n * x * ((4 * n - 1) * x + 5) * (x + 1) ** (n - 3))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * x ** k * k ** 4))

    Eq << Eq[0].this.find(Binomial).apply(discrete.binom.to.mul.binom)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.subs.offset, 1)

    Eq << Eq[-1].this.lhs.find(Pow).apply(algebra.pow.to.mul.split.exponent)

    Eq << Eq[-1].this.find(Add ** 3).apply(algebra.pow.to.add)

    Eq << Eq[-1].this.find(Sum).expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(algebra.sum.to.add.push_front)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(discrete.sum_binom.to.mul.Newton)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.pow.Newton)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.push_front)

    Eq << Eq[-1].this.lhs.apply(algebra.add.collect, factor=x)

    Eq << Eq[-1].this.find(Add).apply(algebra.add.collect, factor=n)

    Eq << Eq[-1].this.lhs.find(Add).apply(algebra.add.collect, factor=n)

    Eq << Eq[-1].this.find(Add[Pow]).apply(algebra.add.collect, factor=(x + 1) ** (n - 2))

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.mul.Newton.trois)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.mul.Newton.deux)

    Eq << Eq[-1].this.find(Mul + Mul).apply(algebra.add.collect, factor=(x + 1) ** (n - 4))

    Eq << Eq[-1].this.find(1 + ~Mul).expand()

    Eq << Eq[-1].this.find(1 + ~Mul[Add]).expand()

    Eq << Eq[-1].this.lhs.find(Add).apply(algebra.add.collect, factor=x * (x + 1) ** (n - 4))

    Eq << Eq[-1].this.rhs.find(Add[Mul]).expand()

    Eq << algebra.eq.given.is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.add.collect, factor=(x + 1) ** (n - 4))

    Eq << Eq[-1].this.lhs.args[1].expand()





if __name__ == '__main__':
    run()
# created on 2021-11-26
