from util import *


@apply
def apply(given):
    eqs, *limits = given.of(All[And])
    return And(*(All(eq, *limits)for eq in eqs))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)

    Eq << apply(All[x:2:b]((x <= 3) & (f(x) >= 1)))

    Eq << algebra.et.given.conds.apply(Eq[1])

    Eq << algebra.all_et.imply.all.apply(Eq[0])


if __name__ == '__main__':
    run()

