from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return Greater(a, b)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b), a.emptySet))

    Eq << ~Eq[1]

    Eq << sets.le.imply.subset.interval.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0])

    Eq << sets.subset.imply.is_empty.apply(Eq[-1])

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].this.lhs.apply(sets.union.to.interval)



if __name__ == '__main__':
    run()
