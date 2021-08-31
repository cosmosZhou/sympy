from util import *



# given e not in S
@apply
def apply(imply):
    e, S = imply.of(NotElement)
    A, B = S.of(Intersection)
    return Or(NotElement(e, B), NotElement(e, A))


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(NotElement(e, B & A))

    Eq << ~Eq[0]

    Eq << Eq[-1].apply(sets.el.imply.et.el.split.intersect)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

