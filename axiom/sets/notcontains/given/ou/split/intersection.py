from util import *



# given e not in S
@apply
def apply(imply):
    e, S = imply.of(NotContains)
    A, B = S.of(Intersection)
    return Or(NotContains(e, B), NotContains(e, A))


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(NotContains(e, B & A))

    Eq << ~Eq[0]

    Eq << Eq[-1].apply(sets.contains.imply.contains.split.intersection)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

