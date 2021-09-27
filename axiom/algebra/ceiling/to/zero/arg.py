from util import *


@apply
def apply(self):
    z = self.of(Ceiling)
    (z, coeff), half = z.of(Arg * Expr - Expr)
    coeff *= S.Pi * 2
    assert coeff <= 1 and coeff >= -1 or 1 / coeff >= 1 or 1 / coeff <= -1
    assert half == S.One / 2
    return Equal(self, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    z = Symbol(complex=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Ceiling(Arg(z) / (2 * S.Pi) / n - S.One / 2))

    Eq << sets.imply.el.arg.apply(z)

    Eq << sets.el.imply.el.div.interval.apply(Eq[-1], n, simplify=None)

    Eq << sets.el.imply.el.sub.apply(Eq[-1], S.Pi, simplify=None)

    Eq << sets.el.imply.el.div.interval.apply(Eq[-1], S.Pi * 2, simplify=None)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq.contains = Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq.le = LessEqual(-1, Eq.contains.rhs.start, plausible=True)

    Eq << Eq.le * (2 * n)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq.ge = GreaterEqual(0, Eq.contains.rhs.stop, plausible=True)

    Eq << Eq.ge * (2 * n)
    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << sets.le.ge.el.imply.el.interval.apply(Eq.le, Eq.ge, Eq.contains)

    Eq << sets.el.imply.ceiling_is_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()