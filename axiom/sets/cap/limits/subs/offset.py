from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Cap, self, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, n, d = Symbol(integer=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cap[n:a:b](f(n)), d)

    Eq << sets.eq.given.et.suffice.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.all_el.st.cap), Eq[-1].this.lhs.apply(sets.el.imply.all_el.st.cap)

    Eq <<= Eq[-2].this.rhs.apply(sets.el.given.all_el.st.cap), Eq[-1].this.rhs.apply(sets.el.given.all_el.st.cap)

    Eq <<= Eq[-2].this.lhs.apply(algebra.all.imply.all.limits.subs.offset, d)

    Eq <<= Eq[-1].this.lhs.apply(algebra.all.imply.all.limits.subs.offset, -d)


if __name__ == '__main__':
    run()