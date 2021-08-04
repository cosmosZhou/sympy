from util import *


@apply
def apply(given):
    e, finiteset = given.of(Contains[FiniteSet])

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from axiom import sets

    e, a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Contains(e, {a, b, c}))

    Eq << sets.ou_eq.imply.contains.finiteset.apply(Eq[1])












if __name__ == '__main__':
    run()