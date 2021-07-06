from util import *


@apply
def apply(given, delta=None, var=None):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    fn, (x, x0, dir) = of_limited(given, real=True)

    M = fn.generate_var(excludes={x}, var=var, positive=True, real=True)
    exists = any_all(Equal(given.lhs, S.Zero), M, delta=delta)

    limits = exists.limits + (M,)
    return exists.func(exists.function, *limits)


@prove
def prove(Eq):
    from axiom import calculus, algebra
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
#     x = Symbol.x(integer=True)

    f = Function.f(real=True, shape=())

    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))

#     x0 = oo
#     x0 = -oo

    a = Symbol.a(real=True)
#     a = oo
#     a = -oo

    direction = 1

    Eq << apply(Contains(Limit[x:x0:direction](f(x)), Reals), var='M')

    M = Eq[-1].variables[1]

    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], var='A')

    A = -Eq[-1].function.function.lhs.arg.args[0]
    Eq << Eq[-1].this.function.function.apply(algebra.lt.imply.et.split.abs)

    Eq << Eq[-1].this.function.function.args[0] + A

    Eq << Eq[-1].this.function.function.args[0] + A

    Eq << Eq[-1].this.function.function.apply(algebra.lt.gt.imply.lt.abs.max)

    Eq << algebra.cond.imply.any.subs.apply(Eq[-1], Eq[-1].function.function.rhs, M)


if __name__ == '__main__':
    run()
