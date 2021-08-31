from util import *



@apply
def apply(given):
    p, q = given.of(Necessary)
    return p | q.invert()


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Necessary(x > y, f(x) > g(y)))

    Eq << Eq[0].reversed

    Eq << Eq[-1].apply(algebra.suffice.imply.ou)


if __name__ == '__main__':
    run()
