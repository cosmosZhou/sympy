from util import *


@apply(given=None)
def apply(given):
    fx, fy = given.of(Suffice)
    return Equivalent(given, Necessary(fy, fx))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Suffice(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.suffice.imply.necessary.reverse)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.given.necessary.reverse)


if __name__ == '__main__':
    run()