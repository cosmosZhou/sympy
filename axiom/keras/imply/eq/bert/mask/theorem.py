from util import *


@apply
def apply(a, Ξ):
    assert a.shape == Ξ.shape
    if Ξ.is_Lamda:
        function, *limits = Ξ.of(Lamda)
    else:
        function, *limits = Ξ.defun().of(Lamda)

    assert function.is_Bool
    return Equal(exp(a - (1 - Ξ) * oo), Ξ * exp(a))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    p = Function(integer=True, shape=())
    a = Symbol(real=True, shape=(n, n))

    i, j = Symbol(integer=True)

    Ξ = Symbol(Lamda[j:n, i:n](Bool(p(i, j) > 0)))
    Eq << apply(a, Ξ)

    a_quote = Symbol.a(a - (1 - Ξ) * oo)
    Eq << a_quote.this.definition

    Eq << Eq[-1][i, j]

    Eq << Eq[-1].this.rhs.args[1].args[1].args[1].args[1].definition

    Eq << Eq[-1].this.rhs.args[1].args[1].args[1].apply(algebra.bool.to.piece, simplify=None)

    Eq << Eq[-1].this.rhs.args[1].args[1].apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piece)

    Eq << algebra.eq.imply.eq.exp.apply(Eq[-1])

    Eq.exp_a = Eq[-1].this.rhs.apply(algebra.exp.to.piece)

    Eq << Eq[0].this.rhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1] * exp(a[i, j])

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.exp_a, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Eq[-1].this.lhs.arg.definition


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2020-12-27
# updated on 2020-12-27
