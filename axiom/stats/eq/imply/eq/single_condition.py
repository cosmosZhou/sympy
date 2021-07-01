from util import *


# given: x | y & z = x
# imply: x | y = x
@apply
def apply(given, wrt=None):

    assert given.is_Equal
    lhs, rhs = given.args
    assert lhs.is_Conditioned
    x, yz = lhs.args
    assert x == rhs

    y, z = yz.args

    if wrt is not None:
        if y.is_Equal:
            y = y.lhs
        if z.is_Equal:
            z = z.lhs

        assert wrt in {y, z}
        return Equal(x | wrt, x)
    return Equal(x | y, x)


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    Eq << apply(Equal(x | y.as_boolean() & z.as_boolean(), x))

    Eq << stats.eq_conditioned.imply.is_nonzero.apply(Eq[0])

    Eq.y_nonzero, Eq.z_nonzero = stats.is_nonzero.imply.et.apply(Eq[-1])

    

    Eq.xy_probability = stats.is_nonzero.imply.eq.bayes.apply(Eq.y_nonzero, x)

    Eq << stats.is_nonzero.imply.eq.bayes.apply(Eq[2], x)

    Eq << Eq[-1].subs(Eq[0])

    z_ = pspace(z).symbol
    Eq <<= stats.integral.to.probability.apply(Integral[z_](Eq[-1].lhs)), \
        stats.integral.to.probability.apply(Integral[z_](Eq[-1].rhs.args[0])), \
        calculus.eq.imply.eq.integral.apply(Eq[-1], (pspace(z).symbol,))

    Eq << Eq[-3].subs(Eq.xy_probability)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(Eq[-4])

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[-1], Eq.y_nonzero)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

