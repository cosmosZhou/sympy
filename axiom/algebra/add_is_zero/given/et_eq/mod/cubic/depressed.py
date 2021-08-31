from util import *


@apply
def apply(is_zero, x=None, d=0):
    from axiom.algebra.add_is_zero.imply.et.suffice.cubic import cubic_coefficient
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
    arg_AB = Piecewise((0, Equal(p * Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))

    if d == 0:
        x0 = A + B
    elif d == 1:
        x0 = A * w + B
    elif d == 2:
        x0 = A * ~w + B
    else:
        ...

    return Equal((arg_p - arg_AB) % 3, d), Equal(x, x0)



@prove
def prove(Eq):
    from axiom import sets, algebra

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x, d=1)

    Eq << sets.imply.el.arg.apply(-p)

    Eq << sets.el.imply.el.div.interval.apply(Eq[-1], 2 * S.Pi / 3)

    Eq << sets.el.imply.el.sub.apply(Eq[-1], S.One / 2)

    Eq << sets.el.imply.el.ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.range.to.finiteset)

    Eq << sets.imply.el.piece.apply(Eq[1].find(Piecewise))

    Eq << sets.el.imply.el.neg.apply(Eq[-1])

    Eq << sets.el.el.imply.el.add.finiteset.apply(Eq[-1], Eq[-3])

    Eq.contains = sets.eq_mod.el.imply.el.sift.apply(Eq[1], Eq[-1])

    Eq <<= Eq[0].cond.this.apply(algebra.add_is_zero.given.et_eq.cubic.depressed, x, 1), Eq[0].cond.this.apply(algebra.add_is_zero.given.et_eq.cubic.depressed, x, -2)

    Eq <<= algebra.cond.cond.imply.cond.subs.apply(Eq[2], Eq[-2]) & algebra.cond.cond.imply.cond.subs.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.ou_eq.given.el.finiteset)
    Eq << algebra.cond.necessary.imply.cond.transit.apply(Eq.contains, Eq[-1])


if __name__ == '__main__':
    run()