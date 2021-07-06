from util import *


@apply
def apply(is_positive, eq, delta=None):
    A = is_positive.of(Expr < 0)
    fx, (x, x0, dir) = eq.of(Equal[Limit, A])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    return Any[delta](All[x:(abs(x - x0) > 0) & ((abs(x - x0) < delta))](fx < A / 2))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol.x(real=True)
    A = Symbol.A(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(A < 0, Equal(Limit[x:x0](f(x)), A))

    epsilon = Symbol.epsilon(positive=True)
    delta = Eq[-1].variable
    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[1], epsilon, delta)

    Eq << algebra.cond.imply.ou.subs.apply(Eq[-1], epsilon, -A / 2)

    Eq << algebra.cond.ou.imply.cond.apply(-Eq[0] / 2, Eq[-1])

    Eq << Eq[-1].this.function.function.apply(algebra.lt.imply.et.split.abs)

    Eq << Eq[-1].this.function.function.apply(algebra.et.imply.cond)

    Eq << Eq[-1].this.function.function.apply(algebra.lt.transposition, index=0)


if __name__ == '__main__':
    run()