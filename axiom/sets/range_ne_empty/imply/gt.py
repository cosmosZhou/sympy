from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << sets.ne_empty.imply.any_el.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(sets.el_range.imply.et)

    Eq << Eq[-1].this.expr.apply(algebra.lt.ge.imply.gt.transit)


if __name__ == '__main__':
    run()
# created on 2018-10-18
