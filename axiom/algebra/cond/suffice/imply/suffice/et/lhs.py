from util import *



@apply
def apply(*given):
    cond, suffice = given
    p, q = suffice.of(Suffice)
    return Suffice(p & cond, q)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)

    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(a > b, Suffice(x > y, f(x) > g(y)))

    Eq << algebra.suffice.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1])

    Eq << algebra.suffice.imply.ou.apply(Eq[1])

    Eq << ~Eq[-1]



if __name__ == '__main__':
    run()
