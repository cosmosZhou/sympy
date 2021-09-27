from util import *


@apply
def apply(set_comprehension_equality, last_element_equality):

    if last_element_equality.lhs.is_Cup:
        last_element_equality, set_comprehension_equality = set_comprehension_equality, last_element_equality
    p = last_element_equality.lhs.base
    n = last_element_equality.rhs

    assert set_comprehension_equality.is_Equal
    assert set_comprehension_equality.lhs._dummy_eq(p[:n].set_comprehension())
    assert set_comprehension_equality.rhs == Range(0, n)

    return Equal(p[:n + 1].set_comprehension(), Range(0, n + 1))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True, given=True)
    p = Symbol(shape=(oo,), integer=True, nonnegative=True, given=True)
    Eq << apply(Equal(p[:n].set_comprehension(), Range(0, n)),
                Equal(p[n], n))

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.union.split, cond=slice(-1))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
