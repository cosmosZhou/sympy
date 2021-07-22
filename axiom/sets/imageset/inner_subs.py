from util import *


@apply
def apply(self):
    expr, (x, et) = self.of(Cup[FiniteSet])
    if et.is_ConditionSet:
        et = et.condition & Contains(x, et.base_set)
    if et.is_And:
        eqs = et._argset
    else:
        eqs = {et}

    for eq in eqs:
        if eq.is_Equal:
            return Equal(self, imageset(x, expr._subs(*eq.args), et).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)

    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(complex=True, shape=(m,))
    g = Function.g(complex=True, shape=(m,))

    h = Function.h(shape=(), real=True)

    Eq << apply(imageset(x, f(x), Equal(f(x), g(x)) & (h(x) > 0)))

    Eq << Eq[0].this.lhs.apply(sets.cup.piecewise)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.piecewise.subs)


if __name__ == '__main__':
    run()

