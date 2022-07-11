from util import *


@apply
def apply(given):
    e, finiteset = given.of(Element[FiniteSet])

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from axiom import sets

    e, a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a, b, c}))

    u = Symbol(FiniteSet(a, b))
    Eq << u.this.definition

    Eq << (u | c.set).this.args[0].definition

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << sets.el_union.imply.ou.apply(Eq[-1], simplify=True)

    Eq << Eq[-1].this.args[1].rhs.definition

    Eq << Eq[-1].this.args[1].apply(sets.el.imply.ou.split.finiteset.two, simplify=None)


if __name__ == '__main__':
    run()

from . import two
# created on 2018-04-26
