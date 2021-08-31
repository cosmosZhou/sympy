from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(Maxima(lhs, *limits).simplify(), Maxima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:a:b](Equal(f(x), g(x))))

    x_ = Symbol.x(domain=Interval(a, b))

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], x, x_)

    Eq << Eq[1].this.lhs.limits_subs(x, x_)

    Eq << Eq[-1].this.rhs.limits_subs(x, x_)

    Eq << Eq[-1].this.lhs.subs(Eq[2])


if __name__ == '__main__':
    run()

