from util import *



@apply
def apply(n, k):
    return Equal(binomial(n, k), binomial(n, n - k))


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(integer=True)
    k = Symbol.k(integer=True)

    Eq << apply(n, k)

    Eq << Eq[-1].this.lhs.apply(discrete.binomial.to.mul)

    Eq << Eq[-1].this.rhs.apply(discrete.binomial.to.mul)


if __name__ == '__main__':
    run()
