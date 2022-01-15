from util import *


@apply
def apply(self, lower=True, upper=None):
    x, [l], [u] = self.of(BandPart)
    n, m = x.shape
    if lower:
        l = Min(l, n - 1)
        
    if upper:
        u = Min(u, m - 1)
     
    return Equal(self, BandPart[l, u](x))


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, n, l, u = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, m), real=True)
    Eq << apply(BandPart[l, u](x))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].this.rhs.defun()

    i = Symbol(domain=Range(n))
    j = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], (i, j))

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1].this.find(Element).apply(sets.el.to.et.split.range)

    Eq << Eq[-1].this.find(Element).apply(sets.el.to.et.split.range)

    Eq << Eq[-1].this.find(-Min).apply(algebra.mul.to.max)

    Eq << Eq[-1].this.find(GreaterEqual[Add, Max]).apply(algebra.ge_max.to.et.ge)

    


if __name__ == '__main__':
    run()
# created on 2022-01-01
