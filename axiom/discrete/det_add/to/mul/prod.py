from util import *


@apply
def apply(n, a):
    i = Symbol(integer=True)
    return Equal(Det(1 + a[:n] * Identity(n)), (1 + Sum[i:0:n](1 / a[i])) * Product[i:0:n](a[i]))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True, given=False)
    a = Symbol(shape=(oo,), complex=True, zero=False)
    Eq << apply(n, a)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.rhs.expand()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << discrete.det.to.sum.expansion_by_minors.apply(Eq.induct.lhs.arg, i=n)

    Eq << Eq.induct.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-1].this.find(Sum)().find(Add).simplify()

    Eq << Eq[-1].this.find(Lamda)().expr.simplify()

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.identity)

    Eq.deduct = (Eq[-1] - Eq[-1].lhs.args[0]).subs(Eq[0])

    Eq << Eq.deduct.find(Product).this.apply(algebra.prod.to.mul.split, cond={n})

    Eq << Eq.deduct.find(Mul, Sum).this.apply(algebra.sum.to.add.pop_back)

    Eq << Eq.deduct.rhs.this.subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.expand()

    Eq << algebra.et.given.et.transit.apply(Eq.deduct & Eq[-1])

    Eq.deduction = Eq[-1].reversed

    D = Eq.deduction.lhs.expr.args[1].arg
    i = Eq.deduction.lhs.variable.copy(domain=Range(0, n))
    D = D._subs(Eq.deduction.lhs.variable, i)
    def column_transformation(*limits):
        n = limits[0][-1]
        (i, *_), (j, *_) = limits
    #return Identity(n) + Lamda[j:n, i:n](Piecewise((0, i < n - 1), (KroneckerDelta(j, n - 1) - 1, True)))
    #return Identity(n) + Lamda[j:n, i:n](Piecewise((KroneckerDelta(j, n - 1) - 1, Equal(i, n - 1)), (0, True)))
        return Identity(n) + Lamda[j:n, i:n](KroneckerDelta(i, n - 1) * (KroneckerDelta(j, n - 1) - 1))
    #return Lamda(Piecewise((KroneckerDelta(i, j), i < n - 1), (2 * KroneckerDelta(j, n - 1) - 1, True)), *limits)
    Eq << (D @ column_transformation(*D.limits)).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.pop_back)

    Eq.split = Eq[-1].this.rhs().find(Mul, Add, KroneckerDelta).simplify()

    Eq << Eq.split.find(Sum).this().find(Add[2]).simplify()

    Eq << Eq.split.find(Sum[2]).this().find(Add[2]).simplify()

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piece.st.two_pieces)

    Eq << Eq.split.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(Lamda[~Add]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piece.swap)

    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piece.invert)

    Eq << Eq[-1].this.find(Add, Lamda)().find(NotElement).simplify()

    Eq << Eq[-1].this.find(Add, Piecewise).apply(algebra.piece.subs, index=1)

    Eq << Eq[-1].this.find(Add, Lamda)().find(ExprCondPair)().expr.simplify()

    Eq.column_transformation = Eq[-1].this.find(ExprCondPair[3])().expr.simplify()

    Eq << discrete.det.to.sum.expansion_by_minors.apply(Eq.column_transformation.rhs, i=i).this.rhs.simplify(deep=True)

    Eq << Eq[-1].this.find(Mul, Piecewise, Add).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.find(Mul, Piecewise, Add).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.find(Mul, Det).doit()

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.limits.subs.offset, -1)

    k = Eq[-1].find(Product).variable
    Eq << Product[k:n](Eq[-1].find(Product).expr).this.apply(algebra.prod.to.mul.split, cond={i})

    Eq.det_lamda = Eq[-2].subs((Eq[-1] / Eq[-1].rhs.args[0]).reversed)

    Eq << Eq.column_transformation.apply(discrete.eq.imply.eq.det)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].this.lhs.args[0].doit()

    Eq << Eq[-1].subs(Eq.det_lamda).apply(algebra.cond.imply.all, i)

    Eq << algebra.et.given.et.subs.all_eq.apply(Eq.deduction & Eq[-1])

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
