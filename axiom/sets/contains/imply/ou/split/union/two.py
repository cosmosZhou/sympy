from util import *
import axiom



@apply
def apply(given, simplify=True):
    assert given.is_Contains
    e, domain = given.args

    A, B = domain.of(Union)

    first = Contains(e, A)
    second = Contains(e, B)

    if simplify:
        first = first.simplify()
        second = second.simplify()

    return Or(first, second)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Contains(e, A | B))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.notcontains.notcontains.imply.notcontains.union)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

