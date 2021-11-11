from util import *


@apply
def apply(given, index=0):
    B, A = given.of(Subset)
    e = B.of(FiniteSet)
    if isinstance(e, tuple):
        e = e[index]

    return Element(e, A)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(complex=True, positive=True)
    A = Symbol(etype=dtype.complex * n)
    x, y = Symbol(complex=True, shape=(n,))
    Eq << apply(Subset({x, y}, A))

    Eq << sets.subset.imply.all_el.apply(Eq[0])
    Eq << algebra.all.imply.cond.subs.apply(Eq[-1], Eq[-1].variable, x)


if __name__ == '__main__':
    run()


from . import piece
# created on 2020-07-27
# updated on 2020-07-27
