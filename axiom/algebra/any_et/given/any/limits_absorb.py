from util import *


@apply
def apply(given, index):
    from axiom.algebra.any_et.imply.any.limits_absorb import limits_absorb
    return limits_absorb(given, index)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo,))

    f = Function.f(shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)

    Eq << apply(Any[x[:n]:f(x[:n]) > 0, x[n]]((g(x[n]) > f_quote(x[:n])) & (h(x[:n + 1]) > 0)), index=0)

    Eq << algebra.any.imply.any_et.single_variable.apply(Eq[1])

    Eq << algebra.any.given.any_et.apply(Eq[0])


if __name__ == '__main__':
    run()

