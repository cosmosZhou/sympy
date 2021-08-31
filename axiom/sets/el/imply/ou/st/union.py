from util import *



@apply
def apply(imply):
    assert imply.is_Element
    e, domain = imply.args
    A, B = domain.of(Union)

    return Or(Element(e, A), Element(e, B))


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B))

    Eq << sets.el.imply.ou.split.union.apply(Eq[0], simplify=False)


if __name__ == '__main__':
    run()

