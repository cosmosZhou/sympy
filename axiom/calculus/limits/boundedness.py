from util import *


@apply
def apply(given):
    lim, a = given.of(Equal)
    expr, (n, *_) = lim.args
    assert n.is_integer
    M = Symbol.M(real=True, positive=True)
    return Any[M](All[n](abs(expr) <= M))


@prove
def prove(Eq):
    from axiom import calculus, algebra
    n = Symbol.n(integer=True)
    x = Symbol.x(real=True, shape=(oo,), given=True)
    a = Symbol.a(real=True, given=True)

    Eq << apply(Equal(Limit[n:oo](x[n]), a))

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[0])

    ε = Eq[-1].function.function.rhs

    Eq << Eq[-1].this.function.function.apply(algebra.lt.imply.lt.abs.max)

    Eq.lt = Eq[-1].subs(ε, S.Half)

    N = Eq.lt.variable

    a_max = Eq.lt.function.function.rhs
    M = Symbol.M(Max(a_max, Maximize[n:N + 1](abs(x[n]))))

    Eq << M.this.definition

    Eq << LessEqual(a_max, M, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq.lt.this.function.function.apply(algebra.lt.le.imply.lt.transit, Eq[-1])

    Eq.less_than = Eq[-1].this.function.function.apply(algebra.lt.imply.le.relaxed)

    Eq << algebra.imply.all_ge.max.apply(Maximize[n:N + 1](abs(x[n])))

    Eq << LessEqual(Maximize[n:N + 1](abs(x[n])), M, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-2].this.function.apply(algebra.ge.le.imply.le.transit, Eq[-1])

    Eq << algebra.any_all.all.imply.any_all.apply(Eq.less_than, Eq[-1])

    Eq << Eq[-1].this.function.simplify()

    Eq << algebra.any.given.any.subs.apply(Eq[1], Eq[1].variable, M)


if __name__ == '__main__':
    run()

