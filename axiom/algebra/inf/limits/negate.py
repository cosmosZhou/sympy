from util import *


@apply
def apply(self):
    expr, (x, *ab) = self.of(Inf)
    if len(ab) == 2:
        a, b = ab
        if x.is_integer:
            limit = (x, 1 - b, 1 - a)
        else:
            limit = (x, -b, -a)
    else:
        [domain] = ab
        limit = (x, -domain)

    return Equal(self, Inf(expr._subs(x, -x), limit))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)))

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition.reversed

    Eq << algebra.eq.imply.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.le_inf.imply.all_any_lt.apply(Eq[-2]), algebra.ge_inf.imply.all_ge.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1]).reversed

    Eq << algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.le_inf.given.all_any_lt.apply(Eq[-2]), algebra.ge_inf.given.all_ge.apply(Eq[-1])
    Eq <<= Eq[-2].this.expr.apply(algebra.any.limits.negate), Eq[-1].this.apply(algebra.all.limits.negate)


if __name__ == '__main__':
    run()