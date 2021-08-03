from util import *



@apply
def apply(*given):
    cond, suffice = given
    p, q = suffice.of(Suffice)
    return Suffice(p, q & cond)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(a > b, Suffice(x > y, f(x) > g(y)))

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq << algebra.suffice.given.ou.apply(Eq[-1])

    Eq << algebra.cond.imply.ou.apply(Eq[0], cond=x <= y)


if __name__ == '__main__':
    run()
