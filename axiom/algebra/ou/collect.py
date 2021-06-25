from util import *


@apply(given=None)
def apply(given, *, cond=None):
    from axiom.algebra.ou.imply.ou.collect import collect
    return Equivalent(given, collect(given, cond))

@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    f = Function.f(real=True)
    h = Function.h(real=True)
    g = Function.g(real=True)
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)) & (y > 0) | Equal(h(x), g(y)) & (y > 0), cond=y > 0)

    Eq << algebra.equivalent.given.cond.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ou.imply.ou.collect, cond=y > 0)
    Eq << Eq[-1].this.lhs.apply(algebra.ou.given.ou.collect, cond=y > 0)


if __name__ == '__main__':
    run()