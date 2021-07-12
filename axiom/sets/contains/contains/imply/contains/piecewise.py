from util import *


@apply
def apply(*given, piecewise=None):
    S = None
    elements = set()
    for eq in given:
        e, _S = eq.of(Contains)
        if S is None:
            S = _S
        else:
            assert _S == S
        elements.add(e)

    for e, _ in piecewise.args:
        assert e in elements

    return Contains(piecewise, S)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True, given=True)

    S = Symbol.S(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    h = Function.h(shape=(), real=True)

    Eq << apply(Contains(f(x), S), Contains(g(x), S), Contains(h(x), S),
                piecewise=Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True)))

    Eq.plausible = Or(Equal(Bool(Contains(f(x), S)), 1) & Contains(x, A),
                      Equal(Bool(Contains(g(x), S)), 1) & Contains(x, B - A),
                      Equal(Bool(Contains(h(x), S)), 1) & NotContains(x, A | B), plausible=True)

    Eq.bool_fx = sets.contains.imply.eq.bool.contains.apply(Eq[0])

    Eq.bool_gx = sets.contains.imply.eq.bool.contains.apply(Eq[1])

    Eq.bool_hx = sets.contains.imply.eq.bool.contains.apply(Eq[2])

    Eq << Eq.plausible.subs(Eq.bool_fx).subs(Eq.bool_gx).subs(Eq.bool_hx)

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq << Eq.plausible.this.args[0].args[1].lhs.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.args[1].args[1].lhs.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.args[2].args[1].lhs.apply(algebra.bool.to.piecewise)

    Eq << sets.ou.imply.contains.piecewise.apply(Eq[-1], wrt=S)


if __name__ == '__main__':
    run()

