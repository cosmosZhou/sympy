from util import *
import axiom



@apply
def apply(given):
    p, q = given.of(Suffice)
    return q


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Suffice(x > y, f(x) > g(y)))

    Eq << Eq[0].this.apply(algebra.suffice.to.ou)

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
