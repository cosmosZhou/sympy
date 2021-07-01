from util import *


@apply
def apply(given):
    e, s = given.of(NotContains)
    return Equal(s, e.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    s = Symbol.s(etype=dtype.integer, given=True)
    e = Symbol.e(integer=True, given=True)

    Eq << apply(NotContains(e, s))

    U = Symbol.U(e.universalSet)

    Eq << All[e:U](NotContains(e, s), plausible=True)

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << sets.all_notcontains.imply.is_emptyset.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.args[0].definition


if __name__ == '__main__':
    run()

