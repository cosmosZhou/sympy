from util import *


@apply
def apply(cup_finiteset_equality, last_element_equality):

    if last_element_equality.lhs.is_Cup:
        last_element_equality, cup_finiteset_equality = cup_finiteset_equality, last_element_equality
    p = last_element_equality.lhs.base
    n = last_element_equality.rhs

    assert cup_finiteset_equality.is_Equal
    assert cup_finiteset_equality.lhs._dummy_eq(p[:n].cup_finiteset())
    assert cup_finiteset_equality.rhs == Range(n)

    return Equal(p[:n + 1].cup_finiteset(), Range(n + 1))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True, given=True)
    p = Symbol(shape=(oo,), integer=True, nonnegative=True, given=True)
    Eq << apply(Equal(p[:n].cup_finiteset(), Range(n)),
                Equal(p[n], n))

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.union.split, cond=slice(-1))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-07-08
