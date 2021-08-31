from util import *


@apply(given=None)
def apply(given, *, cond=None):
    from axiom.algebra.ou.imply.ou.collect import collect
    return Equivalent(given, collect(given, cond))

@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    f, h, g = Function(real=True)
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)) & (y > 0) | Equal(h(x), g(y)) & (y > 0), cond=y > 0)

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ou.imply.ou.collect, cond=y > 0)
    Eq << Eq[-1].this.lhs.apply(algebra.ou.given.ou.collect, cond=y > 0)


if __name__ == '__main__':
    run()
