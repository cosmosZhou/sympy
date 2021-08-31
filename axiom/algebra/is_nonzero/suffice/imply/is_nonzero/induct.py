from util import *


@apply
def apply(f0, suffice, n=None):
    assert n.is_given == False

    f0.of(Unequal[0])
    fn, fn1 = suffice.of(Suffice)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, 0) == f0
    assert n.domain.min() == 0

    return fn


@prove
def prove(Eq):
    from axiom import algebra, discrete, sets

    n = Symbol(integer=True, nonnegative=True, given=False)
    f = Symbol(integer=True, shape=(oo,))
    Eq << apply(Unequal(f[0], 0), Suffice(Unequal(f[n], 0), Unequal(f[n + 1], 0)), n=n)

    D = Symbol(Lamda[n](KroneckerDelta(f[n], 0)))
    Eq.D0_is_zero = Equal(D[0], 0, plausible=True)

    Eq << Eq.D0_is_zero.this.lhs.definition

    Eq.or_statement = Or(Equal(D[n + 1], 0), Equal(D[n], 1), plausible=True)

    Eq << Eq.or_statement.this.args[0].lhs.definition

    Eq << Eq[-1].this.args[0].lhs.definition

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[1].apply(algebra.suffice.imply.ou)

    Eq.is_multiplication_zero = algebra.ou.imply.is_zero.apply(Eq.or_statement)

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    E = Symbol(Identity(m) + Lamda[j:m, i:m](KroneckerDelta(i + 1, j) * -D[j]))
    Eq << E.this.definition

    Eq << (D[:m] @ E).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.expr.expr.args[1].definition

    Eq << Eq[-1].this.rhs.expr.expr.expand()

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.swap)

    Eq << Eq[-1].this.rhs().find(NotElement).simplify()

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.subs)

    Eq << Eq[-1].subs(Eq.D0_is_zero)

    Eq << Eq.is_multiplication_zero.this.lhs.expand()

    Eq << Eq[-1].subs(n, i - 1)

    Eq << Eq[-1].this.args[1].apply(sets.notin.imply.notin.add, 1)

    Eq << algebra.ou.imply.all.apply(Eq[-1], 1)
    Eq << algebra.eq.eq.imply.eq.subs.apply(Eq[-1].reversed, Eq[-5])

    k = Symbol(integer=True)
    E_quote = Symbol("E'", Lamda[j:m, i:m](Piecewise((Product[k:i + 1:j + 1](D[k]), j >= i), (0, True))))
    Eq.D_is_zero = Eq[-1] @ E_quote

    Eq << (E @ E_quote).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.expr.expr.args[0].definition

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << Eq[-1].this.rhs.expr.expr.args[0].definition

    Eq << Eq[-1].this.rhs.expr.expr.expand()

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, 1)

    Eq << (-Eq[-1].rhs.expr.args[0].args[0].expr).this.apply(algebra.mul.to.prod.limits.push_front)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs().expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().expr.simplify(wrt=True)

    Eq << algebra.piece.swap.apply(Eq[-1].rhs.expr)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.identity)

    Eq << Eq.D_is_zero.subs(Eq[-1])

    Eq << Eq[-1][m - 1]

    Eq << Eq[-1].subs(m, n + 1)

    Eq << Eq[-1].this.lhs.definition


if __name__ == '__main__':
    run()

