from util import *


@apply
def apply(given):
    eqs, *limits = given.of(Exists[And])
    return And(*(Exists(eq, *limits) for eq in eqs))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)

    Eq << apply(Exists[x:2:b]((x <= 3) & (f(x) >= 1)))

    Eq << algebra.any_et.imply.any.split.apply(Eq[0])

    Eq << algebra.et.given.conds.apply(Eq[1])


if __name__ == '__main__':
    run()

