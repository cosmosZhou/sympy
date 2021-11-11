from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Inf, self, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= algebra.eq.imply.et.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= algebra.inf_le.imply.all_any_lt.apply(Eq[-3]), algebra.inf_ge.imply.all_ge.apply(Eq[-2]), algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.inf_le.given.all_any_lt.apply(Eq[-2]), algebra.inf_ge.given.all_ge.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(algebra.any.given.any.limits.subs.offset, -t)
    Eq << algebra.all.given.all.limits.subs.offset.apply(Eq[-1], -t)
    


if __name__ == '__main__':
    run()
# created on 2019-10-03
# updated on 2019-10-03
