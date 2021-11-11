from util import *


@apply
def apply(is_nonzero, n, x2):
    x1 = is_nonzero.of(Unequal[0])
    assert n >= 1
    i, j = Symbol(integer=True)
    return Equal(Det([Lamda[j:n + 1](x2 ** j), Lamda[j:n + 1, i:n](j ** i * x1 ** j)]), x1 ** Binomial(n, 2) * (x1 - x2) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    x1, x2 = Symbol(complex=True)
    Eq << apply(Unequal(x1, 0), n, x2)

    Eq << algebra.ne_zero.imply.ne_zero.reciprocal.apply(Eq[0])

    r = Symbol(Eq[-1].lhs * x2)
    Eq << r.this.definition * x1

    Eq << Eq[-1].reversed

    Eq.eq = Eq[1].subs(Eq[-1])

    Eq << Eq.eq.rhs.this.args[1].base.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.find(Binomial).apply(discrete.binomial.to.mul.expand)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).expand()

    Eq << Eq.eq.subs(Eq[-1])

    j, i = Eq[-1].find(Lamda[Tuple, Tuple]).variables
    Eq << (Eq[-1].lhs.arg @ Lamda[j:n + 1, i:n + 1](Eq[2].lhs ** j * KroneckerDelta(i, j))).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_piece.to.blockMatrix)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.det_blockMatrix.to.mul.prod.vandermonde.st.lamda.pow)

    Eq << Eq[-1].subs(r.this.definition)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1] * x1 ** binomial(n, 2)

    Eq << Eq[-1].this.lhs.find(Binomial).apply(discrete.binomial.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.find(Symbol ** Add).expand()

    Eq << Eq[-1] * x1 ** n

    Eq << Eq[-1].this.rhs.find((~Add) ** Symbol).apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(algebra.pow.to.mul.split.base)

    
    


if __name__ == '__main__':
    run()
# created on 2020-10-14
# updated on 2021-10-04