from util import *


@apply
def apply(given):
    fx, fy = given.of(Suffice)
    return Necessary(fy, fx)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Suffice(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.necessary.given.ou.apply(Eq[1])
    Eq << algebra.suffice.imply.ou.apply(Eq[0])


if __name__ == '__main__':
    run()