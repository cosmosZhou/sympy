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

    Eq << Eq[-1].apply(sets.el_intersect.imply.et.el)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# created on 2019-02-06
