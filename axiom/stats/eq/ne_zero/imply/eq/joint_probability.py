from util import *


# given: x | y = x
# imply: x | y & z = x | z
@apply
def apply(equality, unequal):
    if equality.is_Unequal:
        equality, unequal = unequal, equality
    assert unequal.is_Unequal
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero
    _y, z = unequal.lhs.arg.args

    assert equality.is_Equal
    lhs, rhs = equality.args
    if lhs.is_Probability:
        assert rhs.is_Probability
        lhs = lhs.arg
        rhs = rhs.arg

    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs

    if _y != y:
        _y, z = z, _y

    assert _y == y

    if x.is_symbol:
        return Equal(x | y & z, x | z)
    else:
        return Equal(Probability(x, given=y & z), Probability(x, given=z))


@prove
def prove(Eq):
    from axiom import stats
    x, y, z = Symbol(real=True, random=True)

    Eq << apply(Equal(x | y, x), Unequal(Probability(y, z), 0))

    Eq << stats.ne_zero.imply.ne_zero.conditioned.apply(Eq[1], y)

    Eq << stats.eq.ne_zero.imply.eq.condition_probability.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-12-16
