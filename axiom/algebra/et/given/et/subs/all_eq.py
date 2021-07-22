from util import *


@apply
def apply(imply, simplify=True):
    from sympy.concrete.expr_with_limits import ExprWithLimits
    all_eq, cond = imply.of(And)
    (old, new), *limits = all_eq.of(All[Equal])
    limits = tuple(limits)

    for expr in cond.findall(ExprWithLimits):
        if expr.expr._has(old) and expr.limits == limits:
            break
    else:
        return

    function = expr.expr._subs(old, new)
    if simplify:
        function = function.simplify()

    expr_ = expr.func(function, *limits)
    if simplify:
        expr_ = expr_.simplify()

    cond = cond._subs(expr, expr_)

    return all_eq, cond


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True, shape=(oo,))
    b = Symbol.b(integer=True, shape=(oo,))

    S = Symbol.S(etype=dtype.integer)

    Eq << apply(All[i:n](Equal(a[i], b[i])) & Contains(Sum[i:n](a[i]), S))

    Eq << algebra.all_eq.imply.eq.sum.apply(Eq[-2])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

