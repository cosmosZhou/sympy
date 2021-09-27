from util import *


@apply
def apply(given):
    fx, fy = given.of(Suffice)
    return Necessary(fy, fx)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Suffice(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.necessary.imply.suffice.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
