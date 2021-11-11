from util import *


def cubic_root(A):
    res = A.of(Expr ** 3)
    if res is not None:
        return res

    args = []
    for arg in A.of(Mul):
        if arg.is_Pow:
            args.append(arg.of(Expr ** 3))
        elif arg.is_Rational:
            p, q = arg.p, arg.q
            if p < 0:
                p = -p
                p = p ** (S.One / 3)
                p = -p
            elif p == 1:
                ...
            else:
                p = p ** (S.One / 3)

            if not p.is_integer:
                return

            q = q ** (S.One / 3)

            if not q.is_integer:
                return

            args.append(Rational(p, q))
        else:
            return
    return Mul(*args)

@apply
def apply(eq_pow, eq_ceiling):
    A, B = eq_pow.of(Equal)

    A = cubic_root(A)
    B = cubic_root(B)

    A_, B_ = eq_ceiling.of(Equal[Ceiling, Ceiling])
    (k, A_), b = A_.of(Expr * Arg - Expr)
    (_k, B_), _b = B_.of(Expr * Arg - Expr)
    assert _k == k == 3 / (S.Pi * 2)
    assert b == _b == S.One / 2
    assert A_ == Arg(A).arg
    assert B_ == Arg(B).arg
    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Equal(A ** 3, B ** 3), Equal(Ceiling(3 * Arg(A) / (S.Pi * 2) - S.One / 2), Ceiling(3 * Arg(B) / (S.Pi * 2) - S.One / 2)))

    Eq << Eq[-1].this.lhs.apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].this.rhs.apply(algebra.expr.to.mul.expi)

    Eq << algebra.eq.imply.eq.pow.apply(Eq[0], exp=S.One / 3)

    Eq << Eq[-1].this.lhs.apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.rhs.apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.lhs.find(Arg).apply(algebra.arg_pow.to.add)

    Eq << Eq[-1].this.rhs.find(Arg).apply(algebra.arg_pow.to.add)

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1] / Eq[-1].lhs.args[-1]


if __name__ == '__main__':
    run()
# created on 2019-04-26
# updated on 2019-04-26
