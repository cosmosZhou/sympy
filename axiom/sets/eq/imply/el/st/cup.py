from util import *


@apply
def apply(given, index=None):
    from axiom.sets.eq.given.eq.set_comprehension import of_set_comprehension
    cup, s = given.of(Equal)
    x = of_set_comprehension(cup)
    n = x.shape[0]
    assert index >= 0 and index < n
    return Element(x[index], s)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True)
    s = Symbol.A(etype=dtype.integer)
    x = Symbol(integer=True, shape=(oo,))
    i = Symbol(domain=Range(0, n))

    Eq << apply(Equal(x[:n].set_comprehension(), s), index=i)

    Eq << Element(x[i], x[:n].set_comprehension(), plausible=True)

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.union.split, cond={i})

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

