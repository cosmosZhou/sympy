from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Sup, self, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= algebra.eq.imply.et.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= algebra.sup_le.imply.all_le.apply(Eq[-3]), algebra.sup_ge.imply.all_any_gt.apply(Eq[-2]), algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.sup_le.given.all_le.apply(Eq[-2]), algebra.sup_ge.given.all_any_gt.apply(Eq[-1])

    Eq << algebra.all.given.all.limits.subs.offset.apply(Eq[-2], -t)
    Eq << Eq[-1].this.expr.apply(algebra.any.given.any.limits.subs.offset, -t)




if __name__ == '__main__':
    run()
# created on 2019-08-29
# updated on 2019-08-29
