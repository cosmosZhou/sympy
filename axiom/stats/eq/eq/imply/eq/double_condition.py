from util import *




# given: x | y & z = x | y
# imply: x | z = x
@apply
def apply(eq_x_given_yz, z_given_y):
    assert z_given_y.is_Equal
    assert z_given_y.lhs.is_Conditioned
    z, y = z_given_y.lhs.args
    assert z == z_given_y.rhs

    assert eq_x_given_yz.is_Equal
    lhs, rhs = eq_x_given_yz.args
    assert lhs.is_Conditioned
    assert rhs.is_Conditioned

    x, yz = lhs.args
    _x, _y = rhs.args
    assert x == _x
    assert y == _y

    _y, _z = yz.args

    if _y != y:
        _z, _y = _y, _z
    assert _z == z or _z == z.as_boolean()
    assert _y == y

    return Equal(x | z, x)


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y.as_boolean() & z.as_boolean(), x | y), Equal(z | y, z))

    Eq.yz_nonzero = stats.eq_conditioned.imply.ne_zero.apply(Eq[0])

    Eq.y_nonzero = stats.eq_conditioned.imply.ne_zero.apply(Eq[0], reverse=True)

    _, Eq.z_nonzero = stats.ne_zero.imply.et.apply(Eq.yz_nonzero)

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq.yz_nonzero, x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq.y_nonzero, z)

    Eq << Eq[-2].subs(Eq[-1])

    Eq.xy_probability = stats.ne_zero.imply.eq.bayes.apply(Eq.y_nonzero, x)

    Eq << Eq[-1].subs(Eq.xy_probability.reversed)

    Eq << Eq[-1].subs(Eq[1])

    y_ = pspace(y).symbol
    Eq << stats.integral.to.probability.apply(Integral[y_](Eq[-1].lhs))

    Eq << Eq[-1].subs(stats.ne_zero.imply.eq.bayes.apply(Eq.z_nonzero, x))

    Eq << calculus.eq.imply.eq.integral.apply(Eq[-3], (y_,))

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.probability)

    Eq << algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq.z_nonzero)


if __name__ == '__main__':
    run()
# created on 2021-07-14
