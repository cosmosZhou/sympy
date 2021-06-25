from util import *


@apply
def apply(given, wrt=None):
    assert given._has(wrt)
    return Any[wrt](given)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, wrt=e)

    S = Symbol.S(Integers)
    Eq << All[e:S](f(e) > 0, plausible=True)

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Unequal(S, S.etype.emptySet, plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << sets.is_nonemptyset.all.imply.any.apply(Eq[-1], Eq[2])

    Eq << Eq[-1].this.limits[0][1].definition


if __name__ == '__main__':
    run()

from . import subs, conditioned
