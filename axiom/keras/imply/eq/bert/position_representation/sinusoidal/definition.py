from util import *


def sinusoid_position_encoding(n, d, b, inverse=False):
    j = Symbol.j(integer=True)
    i = Symbol.i(integer=True)

    if inverse:
        return Symbol("PE'", Lamda[j:d, i:n](Piecewise((cos(i / b ** (j / d)), (-1) ** j > 0),
                                              (-sin(i / b ** ((j - 1) / d)), True))))
    else:
        return Symbol.PE(Lamda[j:d, i:n](Piecewise((sin(i / b ** (j / d)), (-1) ** j > 0),
                                              (cos(i / b ** ((j - 1) / d)), True))))


@apply
def apply(n, d, b):
    PE = sinusoid_position_encoding(n, d, b)
    j, i = PE.definition.variables

    half_dim = Symbol("d'", d / 2)
    assert half_dim.is_integer
    assert half_dim.type in dtype.integer

    emb = log(b) / half_dim

    indices = Lamda[j:half_dim](j)

    emb = exp(indices * -emb)

    pos = Lamda[i:n](i)

    emb = Lamda[j:half_dim, i:n](pos[i] * emb[j])
    SIN = sin(emb)
    COS = cos(emb)
    emb = Lamda[j:d, i:n](Piecewise((SIN[i, j / 2], (-1) ** j > 0), (COS[i, (j - 1) / 2], True)))

    return Equal(PE, emb)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(positive=True, integer=True)
    b = Symbol.b(positive=True)
    d = Symbol("d_model", integer=True, positive=True, even=True)
    Eq << apply(n, d, b)

    PE = Symbol("PE'", Eq[2].rhs)
    j, i = Eq[2].rhs.variables
    Eq << PE[i, j].this.definition

    Eq << Eq[-1].rhs.args[0].expr.arg.this.args[1].arg.args[1].base.definition

    Eq << Eq[-1].this.rhs.args[1].arg.apply(algebra.mul.to.log)

    Eq << Eq[-3].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].rhs.args[1].expr.arg.this.args[1].arg.args[1].base.definition

    Eq << Eq[-1].this.rhs.args[1].arg.apply(algebra.mul.to.log)

    Eq << Eq[-1].this.rhs.args[0].args[1].expand()

    Eq << Eq[-4].this.rhs.subs(Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, d), (i, 0, n))

    Eq << Eq[0].this.rhs.args[1].expr.arg.args[0].args[1].expand()

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << PE.this.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
