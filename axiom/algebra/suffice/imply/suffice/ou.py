from util import *



@apply
def apply(given, *, cond=None):
    lhs, rhs = given.of(Suffice)
    return Suffice(cond | lhs, cond | rhs)


@prove
def prove(Eq):
    from axiom import algebra
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)

    Eq << apply(Suffice(a > b, f(a) > g(b)), cond=x > y)

    Eq << algebra.suffice.imply.ou.apply(Eq[0])

    Eq << algebra.suffice.given.ou.apply(Eq[1])

    Eq << algebra.ou.given.et.apply(Eq[-1])

    Eq << algebra.ou.given.ou.apply(Eq[-1], Slice[:2])


if __name__ == '__main__':
    run()
