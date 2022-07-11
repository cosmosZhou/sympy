from util import *


def subs(self, x, x0):
    [*args] = self.args

    if self.is_Piecewise:
        for i, (e, c) in enumerate(args):
            if c:
                continue
            if c._subs(x, oo):
                args[i] = (e, True)
                i += 1
                break
        else:
            return self
        return Piecewise(*args)

    hit = False
    for i, arg in enumerate(self.args):
        arg = subs(arg, x, x0)
        if arg == args[i]:
            continue
        args[i] = arg
        hit = True
    if hit:
        return self.func(*args)

    return self

@apply
def apply(self):
    expr, (x, x0, dir) = self.of(Limit)
    assert x0 == oo
    _expr = subs(expr, x, x0)
    assert _expr != expr
    return Equal(self, Limit[x:x0:dir](_expr))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    n = Symbol(integer=True)
    a = Symbol(integer=True, given=True)
    f, g = Function(real=True)
    Eq << apply(Limit[n:oo](Piecewise((f(n), n > a), (g(n), True))))

    A = Symbol(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1].reversed)

    Eq << Eq[-1].this.apply(calculus.eq.to.any_all.limit_definition)

    Eq << Eq[-1].this.find(Less).apply(algebra.lt_piece.given.ou)

    Eq << Eq[-1].this.expr.apply(algebra.all_ou.given.all)

    N = Eq[-1].variable
    Eq << algebra.any.given.any.subs.apply(Eq[-1], N, Max(N, a))

    Eq << Eq[2].this.expr.apply(algebra.all.imply.all.limits.restrict, Range(Max(N + 1, a + 1), oo))

    Eq << Eq[-1].this.find(Max).apply(algebra.max.to.add)

    Eq << Eq[-1].this.expr.apply(algebra.all.imply.all_et)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.imply.et)

    Eq << Eq[-1].this.find(GreaterEqual).apply(algebra.ge.imply.gt.relax)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_max.imply.gt, 1)


if __name__ == '__main__':
    run()
# created on 2020-05-28
