from util import *


@apply
def apply(is_nonzero, x1, m, d):
    x2 = is_nonzero.of(Unequal[0])
    i, j = Symbol(integer=True)
    assert m > d
    return Equal(Det(BlockMatrix([Lamda[j:m, i:d](j ** i * x1 ** j), Lamda[j:m, i:m - d](j ** i * x2 ** j)])), 
                 x2 ** Binomial(m - d, 2) * x1 ** Binomial(d, 2) * (x2 - x1) ** (d * (m - d)) * Product[i:d](factorial(i)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    d = Symbol(integer=True, positive=True)
    m = Symbol(domain=Range(d + 1, oo))
    x1, x2 = Symbol(complex=True)
    Eq << apply(Unequal(x2, 0), x1, m, d)

    Eq << algebra.ne_zero.imply.ne_zero.div.apply(Eq[0])

    r = Symbol(Eq[-1].lhs * x1)
    Eq << r.this.definition * x2

    Eq << Eq[-1].reversed

    Eq << Eq[1].subs(Eq[-1])

    

    

    

    

    j, i = Eq[-1].find(Lamda[Tuple[2]]).variables
    Eq << (Eq[-1].lhs.arg @ Lamda[j:m, i:m](Eq[2].lhs ** j * KroneckerDelta(i, j))).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda_piece.to.block)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.det_block.to.mul.prod.vandermonde.st.lamda.pow.ratio)

    Eq << Eq[-1].subs(r.this.definition)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1] * x2 ** binomial(m, 2)

    Eq << Eq[-1].this.lhs.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.find(Symbol ** ~Add).expand()

    Eq << Eq[-1].this.rhs.find((~Add) ** Mul).apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.rhs.find(Mul ** Mul).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.find(Mul ** Binomial).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.find(Symbol ** Add).find(Binomial).apply(discrete.binom.to.add.st.two, d)

    


if __name__ == '__main__':
    run()
# created on 2022-07-11
