from util import *


@apply
def apply(eq_limit):
    tangent, (epsilon, _0, dir) = eq_limit.of(Equal[Limit, Infinity])
    assert _0 == 0 and dir > 0
    delta = tangent * epsilon
    fx1, fx = delta.of(Expr - Expr)
    for x in fx.free_symbols:
        if fx1 == fx._subs(x, x + epsilon):
            break
    else:
        raise

    return Limit[epsilon:0:1](fx) > fx


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    x, epsilon = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[epsilon:0:1]((f(x + epsilon) - f(x)) / epsilon), oo))

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[0], 'chi')

    Eq << Eq[-1].this.expr.apply(algebra.all.imply.all_et)

    Eq << Eq[-1].this.find(Element).apply(sets.el_interval.imply.gt)

    Eq << Eq[-1].this.expr.expr.apply(algebra.gt_zero.gt.imply.gt.mul)
    Eq << Eq[-1].this.expr.expr.apply(algebra.gt.transport, lhs=0)


if __name__ == '__main__':
    run()
# created on 2020-04-28
