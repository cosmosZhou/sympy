from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    expr, *limits = S.of(Cup)
    return All(NotElement(e, expr).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer, given=True)
    Eq << apply(NotElement(x, Cup[k:n](A[k])))

    Eq << ~Eq[0]

    Eq << sets.el_cup.imply.any_el.apply(Eq[-1], simplify=None)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
