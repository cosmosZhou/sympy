from util import *



@apply
def apply(given):
    p, q = given.of(Suffice)
    return p.invert() | q


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Suffice(x > y, f(x) > g(y)))

    Eq << Eq[0].this.apply(algebra.suffice.to.ou)


if __name__ == '__main__':
    run()
