from util import *


@apply
def apply(is_nonzero, n, x2):
    x1 = is_nonzero.of(Unequal[0])
    assert n >= 3
    k, i, j = Symbol(integer=True)    
    R = Lamda[j:n](x2 ** j)
    A = Lamda[j:n, i:n - 1]((j + 1) ** (i + 1) * x1 ** j)

    return Equal(Det([R, A]), x1 ** Binomial(n, 2) * (x2 - x1) ** n * Product[k:1:n](factorial(k)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(domain=Range(3, oo))
    x1, x2 = Symbol(complex=True)
    Eq << apply(Unequal(x1, 0), n, x2)

    Eq << algebra.is_nonzero.imply.is_nonzero.reciprocal.apply(Eq[0])

    r = Symbol(Eq[-1].lhs * x2)
    Eq << r.this.definition * x1

    Eq << Eq[-1].reversed

    Eq.eq = Eq[1].subs(Eq[-1])

    Eq << Eq.eq.rhs.this.args[1].base.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.find(Binomial).apply(discrete.binomial.to.mul.expand)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).expand()

    Eq << Eq.eq.subs(Eq[-1])


if __name__ == '__main__':
    run()