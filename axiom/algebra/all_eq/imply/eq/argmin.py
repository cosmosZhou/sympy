from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(ArgMin(lhs, *limits).simplify(), ArgMin(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(All[x:a:b](Equal(f(x), g(x))))

    x_ = Symbol.x(domain=Interval(a, b))

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], x, x_)

    Eq << Eq[1].this.lhs.limits_subs(x, x_)

    Eq << Eq[-1].this.rhs.limits_subs(x, x_)

    Eq << Eq[-1].this.lhs.subs(Eq[2])


if __name__ == '__main__':
    run()
