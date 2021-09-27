from util import *



# given e not in S
@apply
def apply(given):
    assert given.is_NotElement
    e, s = given.args
    return Equal(e.set & s, e.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    s = Symbol(etype=dtype.integer, given=True)
    e = Symbol(integer=True, given=True)
    Eq << apply(NotElement(e, s))

    Eq << ~Eq[-1]

    Eq << sets.intersect_is_nonempty.imply.any_el.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

