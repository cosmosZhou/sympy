
from util import *



@apply
def apply(*given):
    contains1, contains2 = given
    assert contains1.is_Contains
    assert contains2.is_Contains

    x, A = contains1.args
    y, _A = contains2.args
    assert A == _A

    return Subset({x, y}, A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(x, S), Contains(y, S))

    Eq << sets.subset.given.all_contains.apply(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.all.to.et.doit.setlimit)

    Eq << algebra.et.given.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()

