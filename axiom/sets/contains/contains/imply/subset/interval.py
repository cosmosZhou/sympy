from util import *


@apply
def apply(contains1, contains2):
    assert contains1.is_Contains
    assert contains2.is_Contains

    x, A = contains1.args
    y, _A = contains2.args
    assert A == _A

    return Subset(Interval(x, y), A)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    S = Interval(a, b, left_open=True)
    Eq << apply(Contains(x, S), Contains(y, S))

    Eq << sets.subset.given.all_contains.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.contains.given.et.split.interval)

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[-1].apply(sets.notcontains.given.ou.split.interval)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.ou, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.et.imply.et.delete, index=-1, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.gt.le.imply.lt.transit)

    Eq << Eq[-1].this.args[1].expr.apply(algebra.et.imply.et.delete, index=1)

    Eq << Eq[-1].this.args[1].expr.apply(algebra.le.ge.imply.le.transit)

    Eq << ~Eq[-1]

    Eq <<= sets.contains.imply.et.split.interval.apply(Eq[0]), sets.contains.imply.et.split.interval.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.args[1].reversed


if __name__ == '__main__':
    run()