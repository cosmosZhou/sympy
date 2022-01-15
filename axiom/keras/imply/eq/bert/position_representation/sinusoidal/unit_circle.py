from util import *


@apply
def apply(n, d, b):
    from axiom.keras.imply.eq.bert.position_representation.sinusoidal.definition import sinusoid_position_encoding
    PE = sinusoid_position_encoding(n, d, b)
    j, k = PE.definition.variables

    (e0, c0), (e1, _) = PE[k, j].definition.args

    F = Symbol(Lamda[j:d, k:n](Piecewise((cos(e0.arg), c0), (e1, True))))

    F_quote = Symbol("F'", Lamda[j:d, k:n](Piecewise((e0, c0), (sin(e1.arg), True))))

    I = S.ImaginaryUnit

    return Equal(abs(F - I * F_quote), OneMatrix(*F.shape))


@prove
def prove(Eq):
    from axiom import algebra, geometry

    n = Symbol(positive=True, integer=True)
    b = Symbol(positive=True)
    d = Symbol("d_model", integer=True, positive=True, even=True)
    Eq << apply(n, d, b)

    Eq << Eq[-1].this.find(Symbol).defun()

    Eq << Eq[-1].this.find(Symbol).defun()

    Eq << Eq[-1].this.find(Lamda ** 2).apply(algebra.pow.to.lamda)

    Eq << Eq[-1].this.find(Lamda ** 2).apply(algebra.pow.to.lamda)

    Eq << Eq[-1].this.find(Add).apply(algebra.add.to.lamda)


    Eq << Eq[-1].this.find(Add).apply(algebra.add_piece.to.piece)

    Eq << Eq[-1].this.find(Cos ** 2).apply(geometry.square_cos.to.add.square_sin)

    Eq << Eq[-1].this.find(Cos ** 2).apply(geometry.square_cos.to.add.square_sin)





if __name__ == '__main__':
    run()
# created on 2021-12-14
# updated on 2021-12-21