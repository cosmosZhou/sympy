from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sup)
    vars = [x for x, *ab in limits]
    const = []
    args = []
    for arg in expr.of(Add):
        if arg.has(*vars):
            args.append(arg)
        else:
            const.append(arg)
    assert const

    const = Add(*const)
    expr = Add(*args)

    return Equal(self, const + Sup(expr, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:m:M](f(x) + h))

    y = Symbol(Eq[0].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq <<= algebra.eq.imply.et.squeeze.apply(Eq[-1]), Eq[0].subs(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.sup_le.imply.all_le.apply(Eq[-3]), algebra.sup_ge.imply.all_any_gt.apply(Eq[-2], z), algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.sup_le.given.all_le.apply(Eq[-2]), algebra.sup_ge.given.all_any_gt.apply(Eq[-1], z)

    Eq << algebra.all.given.all.limits.subs.offset.apply(Eq[-1], h)

    Eq << Eq[-1].this.expr.expr - h


if __name__ == '__main__':
    run()
# created on 2019-09-09
