from util import *


@apply
def apply(subset, piecewise=None):
    args, S = subset.of(Subset[FiniteSet, Set])
    assert {e for e, _ in piecewise.args} == {*args}
    return Element(piecewise, S)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(integer=True, given=True)
    S, A, B = Symbol(etype=dtype.integer, given=True)
    f, g, h = Function(real=True)
    Eq << apply(Subset({f(x), g(x), h(x)}, S),
                piecewise=Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True)))

    sets.subset.imply.el
    Eq << sets.subset.imply.el.apply(Eq[0])
    Eq.bool_fx = sets.el.imply.eq.bool.el.apply(Eq[-1])

    Eq << sets.subset.imply.el.apply(Eq[0], 1)
    Eq.bool_gx = sets.el.imply.eq.bool.el.apply(Eq[-1])

    Eq << sets.subset.imply.el.apply(Eq[0], 2)
    Eq.bool_hx = sets.el.imply.eq.bool.el.apply(Eq[-1])

    Eq.plausible = Or(Equal(Bool(Element(f(x), S)), 1) & Element(x, A),
                      Equal(Bool(Element(g(x), S)), 1) & Element(x, B - A),
                      Equal(Bool(Element(h(x), S)), 1) & NotElement(x, A | B), plausible=True)




    Eq << Eq.plausible.subs(Eq.bool_fx).subs(Eq.bool_gx).subs(Eq.bool_hx)

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq << Eq.plausible.this.args[0].args[1].lhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.args[1].args[1].lhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.args[2].args[1].lhs.apply(algebra.bool.to.piece)

    Eq << sets.ou.imply.el.piece.apply(Eq[-1], wrt=S)


if __name__ == '__main__':
    run()