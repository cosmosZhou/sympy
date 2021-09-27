from util import *


@apply
def apply(given, index=-1):
    (p, q), r = given.of(Suffice >> Boolean)
    return Suffice(p.invert(), r), Suffice(q, r)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Suffice((x > b) >> (x < a), f(x) > g(y)))

    Eq << Eq[0].this.lhs.apply(algebra.suffice.imply.ou)
    Eq << algebra.suffice.given.et.suffice.split.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()