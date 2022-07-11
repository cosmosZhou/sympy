from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    back = function._subs(i, b - 1)
    return Equal(self, Piecewise((Add(Sum[i:a:b - 1](function), back), a <= b - 1), (0, True)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i:0:n + 1](f(i)))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={n})

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap)

    Eq << (n < 0).this.apply(algebra.lt.imply.sum_is_zero, Eq[-1].find(Sum))

    Eq << algebra.infer.imply.eq.piece.apply(Eq[-1], Eq[-2].lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap)
    Eq << Eq[-1].this.find(GreaterEqual).reversed


if __name__ == '__main__':
    run()
# created on 2020-03-25
