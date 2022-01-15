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
    assert unequality.lhs.arg.lhs in {x, y}

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
    from axiom import stats, algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(x.is_independent_of(z), y.is_independent_of(z), Unequal(Probability(y), 0))

    Eq << stats.eq.imply.eq.mul.apply(Eq[0])

    Eq.bayes_yz = stats.eq.imply.eq.mul.apply(Eq[1])

    Eq.z_is_nonzero = stats.eq.imply.ne_zero.apply(Eq[0])

    Eq.bayes_xyz = stats.ne_zero.imply.eq.bayes.apply(Eq.z_is_nonzero, x, y)

    Eq << Eq[2].subs(Eq[1].reversed)

    Eq.given_addition = stats.eq.ne_zero.imply.eq.condition_probability.apply(Eq[0], Eq[-1])

    Eq << stats.ne_zero.imply.ne_zero.joint.apply(Eq[-1])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x)

    Eq << Eq.bayes_xyz.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.bayes_yz)

    Eq << algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq.z_is_nonzero)

    Eq << Eq[-1].subs(Eq.given_addition)

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[2], x)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-12-15
