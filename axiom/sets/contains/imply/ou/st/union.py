from util import *



@apply
def apply(imply):
    assert imply.is_Contains
    e, domain = imply.args
    A, B = domain.of(Union)

    return Or(Contains(e, A), Contains(e, B))


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A | B))

    Eq << sets.contains.imply.ou.split.union.apply(Eq[0], simplify=False)


if __name__ == '__main__':
    run()

