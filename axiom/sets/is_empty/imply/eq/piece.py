from util import *


@apply
def apply(given, peicewise_A, peicewise_B):
    AB = given.of(Equal[EmptySet])
    A, B = AB.of(Intersection)

    (fx, c0_A), (_fx, _) = peicewise_A.of(Piecewise)
    (gx, c0_B), (_gx, _) = peicewise_B.of(Piecewise)

    x, _A = c0_A.of(Element)
    _x, _B = c0_B.of(Element)

    assert x == _x

    if A != _A:
        A, B = B, A

    assert A == _A
    assert B == _B

    return Equal(peicewise_A + peicewise_B, Piecewise((fx + _gx, Element(x, A)),
                                                      (_fx + gx, Element(x, B)),
                                                      (_fx + _gx, True)))


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f, g = Function(shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    g_quote = Function("g'", shape=(), integer=True)
    Eq << apply(Equal(A & B, A.etype.emptySet),
        Piecewise((f(x), Element(x, A)), (f_quote(x), True)),
        Piecewise((g(x), Element(x, B)), (g_quote(x), True)))

    Eq << Eq[1].this.lhs.apply(algebra.add_piece.to.piece)

    Eq << Eq[-1].apply(algebra.cond.given.et.all, cond=Element(x, A))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= Eq[-2].this().expr.simplify(), Eq[-1].this().expr.simplify()



    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-07-04
