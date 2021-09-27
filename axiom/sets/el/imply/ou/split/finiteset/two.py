from util import *



@apply
def apply(given):
    assert given.is_Element
    e, finiteset = given.args
    a, b = finiteset.of(FiniteSet)

    return Or(Equal(e, a), Equal(e, b))


@prove
def prove(Eq):
    from axiom import sets
    e, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a, b}))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.ne.ne.imply.notin, simplify=False)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

