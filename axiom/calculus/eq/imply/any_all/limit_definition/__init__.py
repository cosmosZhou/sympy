from util import *


@apply
def apply(given, ε=None, δ=None):
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    return any_all(given, ε, δ)


@prove
def prove(Eq):
    from axiom import calculus, algebra
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
    x = Symbol.x(integer=True)

    f = Function.f(real=True, shape=())

    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))

    x0 = oo
#     x0 = -oo

    a = Symbol.a(real=True)
#     a = oo
#     a = -oo

    direction = 1

    Eq << apply(Equal(Limit[x:x0:direction](f(x)), a))

    Eq << calculus.eq.to.any_all.limit_definition.apply(Eq[0])

    Eq << algebra.cond.equivalent.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

del limit
from . import limit
