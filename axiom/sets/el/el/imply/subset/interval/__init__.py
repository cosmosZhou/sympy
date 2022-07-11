from util import *


@apply
def apply(contains1, contains2):
    assert contains1.is_Element
    assert contains2.is_Element

    x, A = contains1.args
    y, _A = contains2.args
    assert A == _A

    return Subset(Interval(x, y), A)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, left_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << sets.subset.given.all_el.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.el_interval.given.et)

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[-1].apply(sets.notin_interval.given.ou)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.ou, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.et.imply.et.delete, index=-1, simplify=None)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.gt.le.imply.lt.transit)

    Eq << Eq[-1].this.args[1].expr.apply(algebra.et.imply.et.delete, index=1)

    Eq << Eq[-1].this.args[1].expr.apply(algebra.le.ge.imply.le.transit)

    Eq << ~Eq[-1]

    Eq <<= sets.el_interval.imply.et.apply(Eq[0]), sets.el_interval.imply.et.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.args[1].reversed


if __name__ == '__main__':
    run()
from . import right_open
from . import left_open
# created on 2020-03-31
