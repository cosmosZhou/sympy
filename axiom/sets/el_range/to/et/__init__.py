from util import *


@apply(given=None)
def apply(given):
    x, domain = given.of(Element)
    a, b = domain.of(Range)
    assert x.is_integer
    return Equivalent(given, And(x >= a, x < b))

@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el_range.imply.et, simplify=False)

    Eq << Eq[-1].this.rhs.apply(sets.lt.ge.imply.el.range)


if __name__ == '__main__':
    run()
# created on 2020-03-24

from . import split
