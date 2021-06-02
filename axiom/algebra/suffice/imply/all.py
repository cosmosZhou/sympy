from util import *
import axiom



@apply
def apply(given, wrt=None):
    cond, q = given.of(Suffice)
    if wrt is None:
        wrt = cond.wrt
    return ForAll[wrt:cond](q)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Suffice(x > y, f(x) > g(y)))

    Eq << algebra.suffice.imply.ou.apply(Eq[0])

    Eq << Eq[-1].apply(algebra.ou.imply.all, pivot=1)


if __name__ == '__main__':
    run()
