from util import *


@apply
def apply(self):
    expr, (x, ss) = self.of(Cup[FiniteSet, Tuple[Intersection]])
    return Subset(self, Intersection(*(imageset(x, expr, s) for s in ss)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(complex=True, shape=(m,))
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    Eq << apply(imageset(x, f(x), A & B))

    y = Symbol.y(complex=True, shape=(m,))
    S = Symbol.S(Eq[0].lhs)
    S_quote = Symbol("S'", Eq[0].rhs)
    Eq.suffice = Suffice(Contains(y, S), Contains(y, S_quote), plausible=True)

    Eq << Eq.suffice.this.lhs.rhs.definition

    Eq << Eq[-1].this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(sets.contains.given.et.split.intersection, simplify=False)

    Eq << Eq[-1].apply(algebra.suffice.given.et.suffice)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.rhs.apply(sets.cup.to.union.split, cond=B), Eq[-1].this.rhs.rhs.apply(sets.cup.to.union.split, cond=A)

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.ou.split.union, simplify=False), Eq[-1].this.rhs.apply(sets.contains.given.ou.split.union, simplify=False)

    Eq << sets.suffice.imply.subset.apply(Eq.suffice)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    run()

