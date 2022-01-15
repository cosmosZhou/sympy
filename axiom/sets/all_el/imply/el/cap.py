from util import *


@apply
def apply(given):
    (x, A), *limits = given.of(All[Element])
    return Element(x, Cap(A, *limits))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(positive=True, integer=True, given=False)
    x, k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer)

    Eq << apply(All[k:n](Element(x, A[k])))

    Eq << sets.imply.infer.el.induct.apply(Element(x, A[k]), n)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-01-09
