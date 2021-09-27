from util import *


@apply
def apply(self):
    expr, (x, *ab) = self.of(Sup)
    if len(ab) == 2:
        a, b = ab
        if x.is_integer:
            limit = (x, 1 - b, 1 - a)
        else:
            limit = (x, -b, -a)
    else:
        [domain] = ab
        limit = (x, -domain)
        
    return Equal(self, Sup(expr._subs(x, -x), limit))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)))

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition.reversed

    Eq << algebra.eq.imply.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.le_sup.imply.all_le.apply(Eq[-2]), algebra.ge_sup.imply.all_any_gt.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1]).reversed

    Eq << algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.le_sup.given.all_le.apply(Eq[-2]), algebra.ge_sup.given.all_any_gt.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(algebra.all.limits.negate), Eq[-1].this.expr.apply(algebra.any.limits.negate)


if __name__ == '__main__':
    run()