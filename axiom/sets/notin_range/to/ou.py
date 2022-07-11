from util import *


@apply(given=None)
def apply(given):
    e, S = given.of(NotElement)
    start, stop = S.of(Range)

    lower_bound = e < start
    upper_bound = e >= stop
    return Equivalent(given, Or(lower_bound, upper_bound))


@prove
def prove(Eq):
    from axiom import algebra, sets

    e, a, b = Symbol(integer=True, given=True)
    Eq << apply(NotElement(e, Range(a, b)))

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(sets.notin_range.imply.ou)

    Eq << Eq[-1].this.rhs.apply(sets.ou.imply.notin.range)



if __name__ == '__main__':
    run()
# created on 2021-12-17
