from util import *



# given e not in S
@apply
def apply(imply):
    e, S = imply.of(NotContains)
    A, B = S.of(Union)
    return NotContains(e, A), NotContains(e, B)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(NotContains(e, B | A))

    Eq << sets.notcontains.notcontains.imply.notcontains.union.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()

