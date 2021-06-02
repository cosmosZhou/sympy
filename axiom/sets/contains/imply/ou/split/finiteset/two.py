from util import *
import axiom



@apply
def apply(given):
    assert given.is_Contains
    e, finiteset = given.args
    a, b = finiteset.of(FiniteSet)

    return Or(Equal(e, a), Equal(e, b))


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(e, {a, b}))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.ne.ne.imply.notcontains, simplify=False)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

