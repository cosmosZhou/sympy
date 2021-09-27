from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Sup)    
    return Equal(Sup(fx * a, *limits), a * self)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a > 0, Sup[x:m:M](f(x)))

    Eq.reciprocal = algebra.is_positive.imply.is_positive.div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << algebra.eq.imply.et.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.le_sup.imply.all_le.apply(Eq[-2]), algebra.ge_sup.imply.all_any_gt.apply(Eq[-1], z)

    Eq <<= algebra.all.imply.suffice.apply(Eq[-2]), algebra.all.imply.suffice.apply(Eq[-1])

    Eq <<= algebra.cond.suffice.imply.suffice.et.rhs.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(algebra.is_positive.le.imply.le.mul), algebra.suffice.imply.suffice.et.both_sided.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.cond.any.imply.any_et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.is_positive.gt.imply.gt.mul)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.lt.given.et.scale.positive, a)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.le_sup.given.all_le.apply(Eq[-2]), algebra.ge_sup.given.all_any_gt.apply(Eq[-1], z)

    Eq <<= algebra.all.given.suffice.apply(Eq[-2]), algebra.all.given.suffice.apply(Eq[-1])


if __name__ == '__main__':
    run()