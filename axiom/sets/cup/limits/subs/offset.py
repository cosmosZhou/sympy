from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Cup, self, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, n, d = Symbol(integer=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cup[n:a:b](f(n)), d)

    Eq << sets.eq.given.et.suffice.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.any_el.st.cup), Eq[-1].this.lhs.apply(sets.el.imply.any_el.st.cup)

    Eq <<= Eq[-2].this.rhs.apply(sets.el.given.any_el.st.cup), Eq[-1].this.rhs.apply(sets.el.given.any_el.st.cup)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.subs.offset, d)

    Eq <<= Eq[-1].this.lhs.apply(algebra.any.imply.any.limits.subs.offset, -d)


if __name__ == '__main__':
    run()