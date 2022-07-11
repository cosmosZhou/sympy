from util import *


@apply
def apply(given, index=None):
    from axiom.sets.eq.given.eq.cup.finiteset import of_cup_finiteset
    cup, s = given.of(Equal)
    x = of_cup_finiteset(cup)
    n = x.shape[0]
    assert index >= 0 and index < n
    return Element(x[index], s)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True)
    s = Symbol('A', etype=dtype.integer)
    x = Symbol(integer=True, shape=(oo,))
    i = Symbol(domain=Range(n))

    Eq << apply(Equal(x[:n].cup_finiteset(), s), index=i)

    Eq << Element(x[i], x[:n].cup_finiteset(), plausible=True)

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.union.split, cond={i})

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-08-04
