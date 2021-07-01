from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    assert k.is_Integer
    k = int(k)
    prod = 1
    den = 1 
    for i in range(k):
        prod *= (n - i)
        den *= (i + 1)
    return Equal(self, prod / den)


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol.n(integer=True, positive=True)
    Eq << apply(binomial(n, 3))
    Eq << Eq[-1].this.lhs.apply(discrete.binomial.to.mul.fallingFactorial)


if __name__ == '__main__':
    run()