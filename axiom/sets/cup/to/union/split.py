from util import *


@apply
def apply(self, *, cond, wrt=None, simplify=True):
    from axiom.algebra.sum.to.add.split import split
    return Equal(self, split(Cup, self, cond, wrt=wrt, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(integer=True)
    f = Function(etype=dtype.real)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Cup[x:A](f(x)), cond=B)

    return #the following will result in recursive proving!
    Eq << sets.eq.given.suffice.apply(Eq[0], wrt='y')
    Eq <<= Eq[-2].this.rhs.apply(sets.element.given.ou.split.union), \
    Eq[-1].this.lhs.apply(sets.element.imply.ou.split.union)
    Eq <<= Eq[-2].this.find(Element[Cup]).apply(sets.element.imply.any_contains.st.cup), \
    Eq[-1].this.find(Element[Cup]).apply(sets.element.given.any_contains.st.cup)
    Eq <<= Eq[-2].this.find(Element[Cup]).apply(sets.element.given.any_contains.st.cup), \
    Eq[-1].this.find(Element[Cup]).apply(sets.element.imply.any_contains.st.cup)
    Eq <<= Eq[-2].this.find(Element[Cup]).apply(sets.element.given.any_contains.st.cup), \
    Eq[-1].this.find(Element[Cup]).apply(sets.element.imply.any_contains.st.cup)
    Eq <<= Eq[-2].this.rhs.apply(algebra.ou.given.any), \
    Eq[-1].this.lhs.apply(algebra.ou.imply.any)


if __name__ == '__main__':
    run()

# created on 2018-09-01
# updated on 2018-09-01
