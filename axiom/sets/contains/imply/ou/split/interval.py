from util import *



@apply
def apply(given):
    e, interval = given.of(Contains)
    a, b = interval.of(Range)
    size = b - a
    assert size.is_Integer
    assert size > 0
    finiteset = {a + i for i in range(size)}

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)

    Eq << apply(Contains(e, Range(a, a + 4)))

    Eq << Eq[0].this.rhs.apply(sets.interval.to.finiteset)

    Eq << sets.contains.imply.ou.split.finiteset.apply(Eq[-1])


if __name__ == '__main__':
    run()

