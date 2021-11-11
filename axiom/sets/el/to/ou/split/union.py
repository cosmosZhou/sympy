from util import *


@apply(given=None)
def apply(given, simplify=True):
    assert given.is_Element
    e, domain = given.args

    eqs = [Element(e, s) for s in domain.of(Union)]

    if simplify:
        eqs = [eq.simplify() for eq in eqs]

    return Equivalent(given, Or(*eqs))


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    A, B, C = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Element(e, A | B | C))

    Eq << Eq[0].this.rhs.simplify()


if __name__ == '__main__':
    run()

# created on 2018-08-03
# updated on 2018-08-03
