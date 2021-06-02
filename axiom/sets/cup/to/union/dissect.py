from util import *


@apply
def apply(self, *, cond, wrt=None, simplify=True):
    from axiom.algebra.sum.to.add.dissect import dissect
    assert self.is_Cup
    return Equal(self, dissect(self, cond, wrt=wrt, simplify=simplify))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Cup[x:A](f(x)), cond=B)

    Eq << sets.eq.given.suffice.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.ou.split.union), \
    Eq[-1].this.lhs.apply(sets.contains.imply.ou.split.union)

    Eq <<= Eq[-2].this.find(Contains[Cup]).apply(sets.contains.imply.any_contains.st.cup), \
    Eq[-1].this.find(Contains[Cup]).apply(sets.contains.given.any_contains.st.cup)

    Eq <<= Eq[-2].this.find(Contains[Cup]).apply(sets.contains.given.any_contains.st.cup), \
    Eq[-1].this.find(Contains[Cup]).apply(sets.contains.imply.any_contains.st.cup)

    Eq <<= Eq[-2].this.find(Contains[Cup]).apply(sets.contains.given.any_contains.st.cup), \
    Eq[-1].this.find(Contains[Cup]).apply(sets.contains.imply.any_contains.st.cup)

    Eq <<= Eq[-2].this.rhs.apply(algebra.ou.given.any), \
    Eq[-1].this.lhs.apply(algebra.ou.imply.any)


if __name__ == '__main__':
    run()

