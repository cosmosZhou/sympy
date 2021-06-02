from util import *
import axiom



@apply
def apply(given):
    p, q = given.of(Necessary)
    return p | q.invert()


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Necessary(x > y, f(x) > g(y)))

    Eq << Eq[0].reversed

    Eq << Eq[-1].apply(algebra.suffice.given.ou)


if __name__ == '__main__':
    run()
