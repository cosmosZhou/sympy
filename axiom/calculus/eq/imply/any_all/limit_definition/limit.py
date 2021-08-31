from util import *
from axiom.calculus.eq.to.any_all.limit_definition import any_all



@apply
def apply(given, ε=None, δ=None):
    cond = any_all(given, ε, δ)
    new, old = given.args
    return cond._subs(old, new)


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

    Eq << algebra.cond.equivalent.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
