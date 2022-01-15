from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cap)
    return Equal(self, Cap[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cap[i](f(i)))

    Eq << sets.eq.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cap.imply.all_el, simplify=None), Eq[-1].this.lhs.apply(sets.el_cap.imply.all_el, simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_cap.given.all_el, simplify=None), Eq[-1].this.rhs.apply(sets.el_cap.given.all_el, simplify=None)

    Eq <<= Eq[-2].this.lhs.apply(algebra.all.imply.all.limits.negate, simplify=None), Eq[-1].this.lhs.apply(algebra.all.imply.all.limits.negate, simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-01-23
