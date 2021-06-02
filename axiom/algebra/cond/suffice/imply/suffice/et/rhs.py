from util import *
import axiom



@apply
def apply(*given):
    cond, sufficient = given
    p, q = sufficient.of(Suffice)
    return Suffice(p, q & cond)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(a > b, Suffice(x > y, f(x) > g(y)))

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq[-1])

    Eq << algebra.suffice.given.ou.apply(Eq[-1])

    Eq << algebra.cond.imply.ou.apply(Eq[0], cond=x <= y)


if __name__ == '__main__':
    run()
