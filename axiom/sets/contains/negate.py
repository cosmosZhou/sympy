from util import *


@apply(given=None)
def apply(given):
    x, interval = given.of(Contains)
    return Equivalent(given, Contains(-x, -interval))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))

    Eq << algebra.equivalent.given.cond.apply(Eq[0])

    Eq <<= Eq[-2].apply(algebra.suffice.given.ou), Eq[-1].apply(algebra.necessary.given.ou)

    Eq << Eq[-2].this.args[0].apply(sets.contains.given.contains.neg)

    Eq << Eq[-1].this.args[1].apply(sets.contains.given.contains.neg)


if __name__ == '__main__':
    run()

