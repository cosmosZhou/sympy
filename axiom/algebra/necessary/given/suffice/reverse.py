from util import *


@apply
def apply(given):
    fx, fy = given.of(Necessary)
    return Suffice(fy, fx)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Necessary(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.suffice.imply.necessary.reverse.apply(Eq[1])

    


if __name__ == '__main__':
    run()