from util import *


@apply
def apply(given, wrt=None):
    AB = given.of(Equal[EmptySet])

    A, B = AB.of(Intersection)
    if wrt is None:
        wrt = given.generate_var(**A.etype.dict)

    return All[wrt:A](NotContains(wrt, B))


@prove
def prove(Eq):
    from axiom import sets
    B = Symbol.B(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(Equal(A & B, A.emptySet))

    Eq << ~Eq[1]

    Eq << sets.any.imply.any_et.single_variable.apply(Eq[-1])

    Eq << sets.any_contains.imply.is_nonemptyset.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

