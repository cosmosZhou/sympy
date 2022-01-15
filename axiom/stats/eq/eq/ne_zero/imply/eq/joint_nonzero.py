from util import *




# given: Probability(x | z) = Probability(x) and Probability(y | z) = Probability(y)
# imply: Probability(x & y) | Probability(z) = Probability(x & y)
@apply
def apply(given_x, given_y, unequality):
    assert given_x.is_Equal
    assert given_y.is_Equal
    assert unequality.is_Unequal
    assert unequality.rhs.is_zero

    x = given_x.rhs
    y = given_y.rhs
    assert unequality.lhs.arg == x.as_boolean() & y.as_boolean()

    eq = given_x.lhs
    assert eq.is_Conditioned
    _x, z = eq.args

    eq = given_y.lhs
    assert eq.is_Conditioned
    _y, _z = eq.args

    assert x == _x
    assert y == _y
    assert z == _z

    assert x.is_random and y.is_random and z.is_random
    return Equal(Probability(x, y, given=z), Probability(x, y))


@prove
def prove(Eq):
    from axiom import stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(x.is_independent_of(z), y.is_independent_of(z), Unequal(Probability(x, y), 0))

    Eq << stats.ne_zero.imply.et.apply(Eq[2])



    Eq << stats.eq.eq.ne_zero.imply.eq.nonzero.apply(Eq[0], Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-12-16
