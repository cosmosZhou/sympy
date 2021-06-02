from util import *


import axiom


@apply
def apply(self):
    (s, et), (emptyset, _) = self.of(Piecewise)
    assert emptyset.is_EmptySet

    eqs = et.of(And)

    return Equal(self, Intersection(*(Piecewise((s, eq), (s.etype.emptySet, True)) for eq in eqs)))


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    s = Function.s(etype=dtype.complex * n)

    x = Symbol.x(complex=True, shape=(n,))

    f = Function.f(integer=True, shape=())
    g = Function.g(integer=True, shape=())

    Eq << apply(Piecewise((s(x), (f(x) > 0) & (g(x) > 0)), (x.emptySet, True)))

    t = Symbol.t(complex=True, shape=(n,))
    Eq << sets.eq.given.suffice.apply(Eq[0], wrt=t)

    Eq <<= Eq[-2].this.find(Contains).apply(sets.contains.imply.ou.st.piecewise), \
    Eq[-1].this.find(Contains).apply(sets.contains.imply.contains.split.intersection)

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.contains.split.intersection, simplify=False),\
    Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.ou.st.piecewise)

    Eq <<= Eq[-2].this.rhs.find(Contains).apply(sets.contains.given.ou.st.piecewise), \
    Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.ou.st.piecewise)

    Eq << Eq[-2].this.rhs.apply(sets.contains.given.ou.st.piecewise)

    Eq << Eq[-1].this.rhs.apply(sets.contains.given.ou.st.piecewise)

if __name__ == '__main__':
    run()


