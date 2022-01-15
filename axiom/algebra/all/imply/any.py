from util import *


@apply
def apply(given):
    function, *limits = given.of(All)
    for limit in limits:
        x, *ab = limit
        if len(ab) == 1:
            domain = ab[0]
            assert Equal(domain, domain.etype.emptySet) == False
        elif len(ab) == 2:
            a, b = ab
            assert not a.shape and not a.is_set and a.is_extended_real
            assert not b.shape and not b.is_set and b.is_extended_real
            assert a <= b

    return Any(function, *limits)


@prove
def prove(Eq):
    from axiom import sets
    S = Range(oo)
    e = Symbol(integer=True)
    f = Function(integer=True, shape=())
    Eq << apply(All[e:S](f(e) > 0))

    Eq << Unequal(S, S.etype.emptySet, plausible=True)

    Eq << sets.ne_empty.all.imply.any.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-12-18
