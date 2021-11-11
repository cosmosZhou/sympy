from util import *


@apply
def apply(given, epsilon=None, delta=None):
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    return any_all(given, epsilon, delta)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    n = Symbol(integer=True, positive=True)
    x, x0, a = Symbol(real=True)
    #x = Symbol.x(real=True, shape=(n,))
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    #x0 = Symbol.x0(real=True, shape=(n,))
    x0 = oo
    #x0 = -oo
    #a = oo
    #a = -oo
    direction = 1
    Eq << apply(Equal(Limit[x:x0:direction](f(x)), a))

    Eq << calculus.eq.to.any_all.limit_definition.apply(Eq[0])

    Eq << algebra.cond.iff.imply.cond.transit.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-04-26
# updated on 2020-04-26
