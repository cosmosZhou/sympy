from util import *


@apply
def apply(given, index=None):
    from axiom.sets.eq.given.eq.set_comprehension import of_set_comprehension
    cup, s = given.of(Equal)
    x = of_set_comprehension(cup)
    n = x.shape[0]
    assert index >= 0 and index < n
    return Contains(x[index], s)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True)
    s = Symbol.A(etype=dtype.integer)
    x = Symbol.x(integer=True, shape=(oo,))
    i = Symbol.i(domain=Range(0, n))

    Eq << apply(Equal(x[:n].set_comprehension(), s), index=i)

    Eq << Contains(x[i], x[:n].set_comprehension(), plausible=True)

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.union.split, cond={i})

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

