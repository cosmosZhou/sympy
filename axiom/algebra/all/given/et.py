from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from axiom.algebra.all.imply.et.split import split_all
    return split_all(given, cond, wrt)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    d = Symbol.d(real=True, positive=True)
    f = Function.f(integer=True)
    Eq << apply(All[x:-d:d](f(x) > 0), cond=x > 0)

    Eq << Eq[-1].apply(algebra.all.all.imply.all.limits_union)


if __name__ == '__main__':
    run()

