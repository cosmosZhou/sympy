from util import *


@apply
def apply(given, *, cond=None):
    from axiom.algebra.ou.imply.ou.collect import collect
    return collect(given, cond)


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

    Eq << Eq[1].this.args[0].apply(algebra.et.imply.ou, simplify=None)


if __name__ == '__main__':
    run()
