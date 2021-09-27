from util import *


@apply
def apply(is_negative, self):
    a = is_negative.of(Expr < 0)
    fx, *limits = self.of(Inf)
    return Equal(self, a * Sup(fx / a, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < 0, Inf[x:m:M](f(x) * a))

    Eq.reciprocal = algebra.is_negative.imply.is_negative.div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << algebra.eq.imply.et.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.le_sup.imply.all_le.apply(Eq[-2]), algebra.ge_sup.imply.all_any_gt.apply(Eq[-1], z)

    Eq <<= algebra.all.imply.suffice.apply(Eq[-2]), algebra.all.imply.suffice.apply(Eq[-1])

    Eq <<= algebra.cond.suffice.imply.suffice.et.rhs.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(algebra.is_negative.le.imply.ge.mul), algebra.suffice.imply.suffice.et.both_sided.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.cond.any.imply.any_et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.is_negative.gt.imply.lt.mul)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.lt.given.et.scale.negative, a)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.le_inf.given.all_any_lt.apply(Eq[-2], z), algebra.ge_inf.given.all_ge.apply(Eq[-1])

    Eq <<= algebra.all.given.suffice.apply(Eq[-2]), algebra.all.given.suffice.apply(Eq[-1])


if __name__ == '__main__':
    run()