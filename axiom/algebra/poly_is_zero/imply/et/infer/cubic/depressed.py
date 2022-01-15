from util import *


@apply
def apply(is_zero, x=None):
    from axiom.algebra.poly_is_zero.imply.et.infer.cubic import cubic_coefficient
    fx = is_zero.of(Equal[0])
    _1, _0, p, q = cubic_coefficient(fx, x=x)
    assert _0 == 0 and _1 == 1

    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)

    w = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    arg_p = Ceiling(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    #arg_AB = Ceiling(3 * Arg(A * B) / (S.Pi * 2) - S.One / 2)

    arg_AB = Piecewise((0, Equal(p * Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))

    d = arg_p - arg_AB
    return Infer(Equal(d, 0), Equal(x, A + B) | Equal(x, A * w + B * ~w) | Equal(x, A * ~w + B * w)), Infer(Equal(d % 3, 1), Equal(x, A * w + B) | Equal(x, A * ~w + B * ~w) | Equal(x, A + B * w)), Infer(Equal(d % 3, 2), Equal(x, A * ~w + B) | Equal(x, A + B * ~w) | Equal(x, A * w + B * w))



@prove
def prove(Eq):
    from axiom import sets, algebra

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x)

    Eq << sets.imply.el.arg.apply(-p)

    Eq << sets.el.imply.el.mul.interval.apply(Eq[-1], 3, simplify=None)

    Eq << sets.el.imply.el.sub.apply(Eq[-1], S.Pi, simplify=None)

    Eq << sets.el.imply.el.div.interval.apply(Eq[-1], S.Pi * 2, simplify=None)

    Eq << sets.el.imply.el.ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(sets.range.to.finiteset)

    Eq << sets.imply.el.piece.apply(Eq[1].find(Piecewise))

    Eq << sets.el.imply.el.neg.apply(Eq[-1])

    Eq << sets.el.el.imply.el.add.finiteset.apply(Eq[-1], Eq[-3])

    V = Eq[-1].find(Arg[Add]).arg
    U = Eq[-1].find(Arg[2]).arg
    Eq.eq_peicewise = algebra.ceiling_arg.to.piece.apply(Eq[-1].find(Ceiling)._subs(-p, U ** (S.One / 3) * V ** (S.One / 3)))

    Eq << Eq[-1].subs(Eq.eq_peicewise.reversed)

    Eq.ou = sets.el.imply.ou.split.finiteset.apply(Eq[-1])

    Eq <<= Eq.ou & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.args[0].apply(algebra.poly_is_zero.eq_ceiling.imply.cubic, x, ret=1)

    Eq << Eq[-1].this.args[1].apply(algebra.poly_is_zero.eq_ceiling.imply.cubic, x, ret=1)

    Eq << Eq[-1].this.args[2].apply(algebra.poly_is_zero.eq_ceiling.imply.cubic, x, ret=1)

    Eq << Eq[-1].this.args[3].apply(algebra.poly_is_zero.eq_ceiling.imply.cubic, x, ret=1)

    Eq << Eq[-1].this.args[4].apply(algebra.poly_is_zero.eq_ceiling.imply.cubic, x, ret=1)

    Eq << Eq[-1].this.args[3:].apply(algebra.ou.imply.et.collect)

    Eq << Eq[-1].this.args[:2].apply(algebra.ou.imply.et.collect)

    Eq << Eq[-1].this.find(Equal[Integer] | Equal[Integer]).apply(algebra.ou_eq.imply.eq.mod)

    Eq << Eq[-1].this.find(Equal[Integer] | Equal[Integer]).apply(algebra.ou_eq.imply.eq.mod)

    Eq << Eq[-1].this.find(Equal[Ceiling, Ceiling]).apply(algebra.eq.imply.mod_is_zero, 3, swap=True)

    Eq << Eq[-1].subs(Eq.eq_peicewise)

    Eq << algebra.ou.imply.et.infer.apply(Eq[-1])

    Eq << Eq[1].this.lhs.apply(algebra.eq.imply.mod_is_zero, 3)


if __name__ == '__main__':
    run()
# created on 2018-11-24
