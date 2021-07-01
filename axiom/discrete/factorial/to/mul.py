from util import *


@apply
def apply(self):
    n = self.of(Factorial)
    assert n > 0
    return Equal(self, n * factorial(n - 1))


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(factorial(n))

    Eq << Eq[0].this.find(factorial).apply(discrete.factorial.to.product)

    Eq << Eq[-1].this.find(factorial).apply(discrete.factorial.to.product)

    Eq << Eq[-1].this.lhs.split({n})


if __name__ == '__main__':
    run()
