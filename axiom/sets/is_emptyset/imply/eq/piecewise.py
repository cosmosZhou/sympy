from util import *


@apply
def apply(given, peicewise_A, peicewise_B):
    AB = given.of(Equal[EmptySet])
    A, B = AB.of(Intersection)

    (fx, c0_A), (_fx, _) = peicewise_A.of(Piecewise)
    (gx, c0_B), (_gx, _) = peicewise_B.of(Piecewise)

    x, _A = c0_A.of(Contains)
    _x, _B = c0_B.of(Contains)

    assert x == _x

    if A != _A:
        A, B = B, A

    assert A == _A
    assert B == _B

    return Equal(peicewise_A + peicewise_B, Piecewise((fx + _gx, Contains(x, A)),
                                                      (_fx + gx, Contains(x, B)),
                                                      (_fx + _gx, True)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    g_quote = Function("g'", shape=(), integer=True)
    Eq << apply(Equal(A & B, A.etype.emptySet),
        Piecewise((f(x), Contains(x, A)), (f_quote(x), True)),
        Piecewise((g(x), Contains(x, B)), (g_quote(x), True)))

    Eq << Eq[1].this.lhs.apply(algebra.add.to.piecewise.st.two_pieces)

    Eq << Eq[-1].apply(algebra.cond.given.et.all, cond=Contains(x, A))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-1].this().function.simplify()

    Eq << Eq[-2].this().function.simplify()

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

