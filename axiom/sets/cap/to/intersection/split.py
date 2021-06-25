from util import *


@apply
def apply(self, indices, wrt=None, *, simplify=True):
    from axiom.algebra.sum.to.add.split import split
    assert self.is_Cap
    return Equal(self, split(self, indices, wrt=wrt, simplify=simplify))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Cap[x:A](f(x)), B)

    Eq << sets.eq.given.suffice.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.contains.split.intersection, simplify=False), \
    Eq[-1].this.lhs.apply(sets.contains.imply.contains.split.intersection)

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.all_contains.st.cap), \
    Eq[-1].this.rhs.apply(sets.contains.given.all_contains.st.cap)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.all_contains.st.cap), \
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.all_contains.st.cap)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.all_contains.st.cap), \
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.all_contains.st.cap)

    Eq <<= Eq[-2].this.rhs.apply(algebra.et.given.all.limits_union), \
    Eq[-1].this.lhs.apply(algebra.all.all.imply.all.limits_union)


if __name__ == '__main__':
    run()

