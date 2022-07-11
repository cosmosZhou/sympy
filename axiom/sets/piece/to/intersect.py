from util import *


@apply
def apply(self):
    (s, et), (empty, _) = self.of(Piecewise)
    assert empty.is_EmptySet

    eqs = et.of(And)

    return Equal(self, Intersection(*(Piecewise((s, eq), (s.etype.emptySet, True)) for eq in eqs)))


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    s = Function(etype=dtype.complex * n)

    x, t = Symbol(complex=True, shape=(n,))

    f, g = Function(integer=True, shape=())

    Eq << apply(Piecewise((s(x), (f(x) > 0) & (g(x) > 0)), (x.emptySet, True)))

    Eq << sets.eq.given.et.infer.apply(Eq[0], wrt=t)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_piece.imply.ou), \
    Eq[-1].this.find(Element).apply(sets.el_intersect.imply.et.el)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_intersect.given.et.el, simplify=False), \
    Eq[-1].this.lhs.find(Element).apply(sets.el_piece.imply.ou)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(sets.el_piece.given.ou), \
    Eq[-1].this.lhs.find(Element).apply(sets.el_piece.imply.ou)

    Eq << Eq[-2].this.rhs.apply(sets.el_piece.given.ou)

    Eq << Eq[-1].this.rhs.apply(sets.el_piece.given.ou)


if __name__ == '__main__':
    run()

# created on 2018-09-25
