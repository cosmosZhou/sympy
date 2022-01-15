from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cup)
    return Equal(self, Cup[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i](f(i)))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_cup.given.any_el), Eq[-1].this.lhs.apply(sets.el_cup.imply.any_el)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.negate.infinity)

    Eq <<= Eq[-1].this.lhs.apply(algebra.any.imply.any.limits.negate.infinity)


if __name__ == '__main__':
    run()
# created on 2018-10-05
