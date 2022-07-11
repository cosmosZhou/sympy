from util import *


@apply
def apply(given, x=None):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    from axiom.algebra.poly_is_zero.imply.et.infer.cubic import cubic_coefficient
    _1, a, b, c = cubic_coefficient(fx, x=x)
    assert _1 == 1
    q = a ** 3 / 27 * 2 + c - a * b / 3
    p = b - a ** 2 / 3
    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    arg_p = Ceiling(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    #arg_AB = Ceiling(3 * Arg(A * B) / (S.Pi * 2) - S.One / 2)
    arg_AB = Piecewise((0, Equal(p * Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))
    d = arg_p - arg_AB

    return Infer(Equal(d, 0), Or(Equal(x, A + B - a / 3), Equal(x, A * w + B * ~w - a / 3), Equal(x, A * ~w + B * w - a / 3))), \
            Infer(Equal(d % 3, 1), Or(Equal(x, A * w + B - a / 3), Equal(x, A * ~w + B * ~w - a / 3), Equal(x, A + B * w - a / 3))), \
            Infer(Equal(d % 3, 2), Or(Equal(x, A * ~w + B - a / 3), Equal(x, A + B * ~w - a / 3), Equal(x, A * w + B * w - a / 3)))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x)

    x = Symbol(x + a / 3)
    Eq.x_def = x.this.definition

    Eq << Eq.x_def.this.apply(algebra.eq.transport, rhs=0).reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << algebra.poly_is_zero.imply.et.infer.cubic.depressed.apply(Eq[-1], x=x)

    Eq <<= Eq[-3].subs(Eq.x_def), Eq[-2].subs(Eq.x_def), Eq[-1].subs(Eq.x_def)

    Eq <<= Eq[-3].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0), Eq[-2].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0), Eq[-1].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0)

    Eq <<= Eq[-3].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0), Eq[-2].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0), Eq[-1].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0)

    Eq <<= Eq[-3].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0), Eq[-2].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0), Eq[-1].this.find(Equal[Add, Add]).apply(algebra.eq.transport, lhs=0)


if __name__ == '__main__':
    run()
# created on 2018-11-25
