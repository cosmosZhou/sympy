from util import *


@apply
def apply(n, d, b):
    from axiom.keras.imply.eq.bert.position_representation.sinusoidal.definition import sinusoid_position_encoding
    PE = sinusoid_position_encoding(n, d, b)
    j, i = PE.definition.variables

    k = Symbol(integer=True)

    PE_quote = sinusoid_position_encoding(n, d, b, inverse=True)

    (e0, c0), (e1, _) = PE[k, j].definition.args

    F = Symbol(Lamda[j:d, k:n](Piecewise((cos(e0.arg), c0), (e1, True))))

    F_quote = Symbol("F'", Lamda[j:d, k:n](Piecewise((e0, c0), (sin(e1.arg), True))))

    I = S.ImaginaryUnit
    z = Symbol(F - I * F_quote)

    Z = Symbol(PE * I - PE_quote)

    return Equal(Z[i + k], Z[i] * z[1] ** k)


@prove
def prove(Eq):
    from axiom import algebra, geometry

    n = Symbol(positive=True, integer=True)
    b = Symbol(positive=True)
    d = Symbol("d_model", integer=True, positive=True, even=True)
    Eq << apply(n, d, b)

    PE_quote = Eq[0].lhs.base
    PE = Eq[1].lhs.base
    i, j = Eq[0].lhs.indices
    k = Eq[3].lhs.indices[0]
    Eq.PE_definition = PE[i + k, j].this.definition

    Eq.PE_quote_definition = PE_quote[i + k, j].this.definition

    Eq << Eq.PE_definition.rhs.args[0].expr.this.arg.apply(algebra.mul.to.add)

    Eq << Eq.PE_definition.rhs.args[1].expr.this.arg.apply(algebra.mul.to.add)

    Eq <<= Eq[-2].this.rhs.apply(geometry.sin.to.add.principle), Eq[-1].this.rhs.apply(geometry.cos.to.add.principle)

    Eq.cossin = Eq.PE_definition.this.rhs.subs(Eq[-2], Eq[-1])

    Eq << Eq[1] * Eq[3]

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[0] * Eq[4]

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1] + Eq[-3]

    Eq << Eq[-1].this.rhs.apply(algebra.add_piece.to.piece)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.cossin, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, d))

    Eq.PE_equality = Eq[-1].this.rhs.apply(algebra.lamda.to.add)

    Eq << Eq.PE_quote_definition.rhs.args[0].expr.this.arg.apply(algebra.mul.to.add)

    Eq << Eq.PE_quote_definition.rhs.args[1].expr.args[1].this.arg.apply(algebra.mul.to.add)

    Eq <<= Eq[-2].this.rhs.apply(geometry.cos.to.add.principle), Eq[-1].this.rhs.apply(geometry.sin.to.add.principle)

    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq[-2])

    Eq << Eq.PE_quote_definition.this.rhs.subs(Eq[-3])

    Eq.coscos = Eq[-1].this.rhs.subs(Eq[-3])

    Eq << Eq[1] * Eq[4]

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[0] * Eq[3]

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1] - Eq[-3]

    Eq << Eq[-1].this.rhs.apply(algebra.add_piece.to.piece)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.coscos, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, d))

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.add)

    I = S.ImaginaryUnit
    Eq << I * Eq.PE_equality - Eq[-1]

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.collect(PE[i])

    Eq.collect = Eq[-1].this.rhs.collect(PE_quote[i])

    z = Eq[5].lhs
    Eq << z[k].this.definition

    Eq << Eq[-1] * I

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq.collect.subs(Eq[-1].reversed, Eq[-3].reversed)

    Eq << Eq[-1].this.rhs.collect(z[k])

    Z = Eq[2].lhs
    Eq << Z[i].this.definition

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Z[k + i].this.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(k, 1)

    Eq << algebra.eq.imply.eq.geometric_progression.apply(Eq[-1], n=i)

    Eq << Eq[-1].subs(i, i + k)

    Eq << Eq[-2] * z[1] ** k

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2020-12-31
