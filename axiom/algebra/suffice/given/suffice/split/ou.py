from util import *



@apply
def apply(given):
    ou, fx = given.of(Suffice)
    eqs = ou.of(Or)
    return tuple(Suffice(eq, fx) for eq in eqs)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    b = Symbol.b(integer=True)
    a = Symbol.a(integer=True)

    Eq << apply(Suffice((a > b) | (f(a) > f(b)), f(x) > g(x)))

    Eq << algebra.suffice.suffice.imply.suffice.ou.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()
