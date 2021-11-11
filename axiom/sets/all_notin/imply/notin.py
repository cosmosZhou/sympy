from util import *


@apply
def apply(given):
    (e, S), *limits = given.of(All[NotElement])

    return NotElement(e, Cup(S, *limits))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    x, k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer)

    Eq << apply(All[k:n](NotElement(x, A[k])))

    Eq << sets.imply.infer.notin.induct.apply(Eq[0].expr, n)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-09-08
# updated on 2018-09-08
