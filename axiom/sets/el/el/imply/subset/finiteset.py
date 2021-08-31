from util import *



@apply
def apply(contains1, contains2):
    assert contains1.is_Element
    assert contains2.is_Element

    x, A = contains1.args
    y, _A = contains2.args
    assert A == _A

    return Subset({x, y}, A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x, y = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)

    Eq << apply(Element(x, S), Element(y, S))

    Eq << sets.subset.given.all_el.apply(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.all.to.et.doit.setlimit)

    Eq << algebra.et.given.et.apply(Eq[-1])


if __name__ == '__main__':
    run()

