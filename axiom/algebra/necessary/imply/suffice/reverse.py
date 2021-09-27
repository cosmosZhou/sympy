from util import *


@apply
def apply(given):
    fx, fy = given.of(Necessary)
    return Suffice(fy, fx)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Necessary(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.suffice.given.ou.apply(Eq[1])
    Eq << algebra.necessary.imply.ou.apply(Eq[0])




if __name__ == '__main__':
    run()
