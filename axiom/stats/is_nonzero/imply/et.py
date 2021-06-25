from util import *


@apply
def apply(given, wrt=None):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero

    eqs = given.lhs.arg
    assert eqs.is_And
    if wrt is not None:
        lhs, rhs = [], []
        for eq in eqs.args:
            if eq.lhs in wrt:
                rhs.append(eq)
            else:
                lhs.append(eq)
        lhs = And(*lhs)
        rhs = And(*rhs)
        return And(Unequal(Probability(lhs), 0), Unequal(Probability(rhs), 0))
    else:
        return And(*[Unequal(Probability(eq), 0) for eq in eqs.args])


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y), 0))

    _x = pspace(x).symbol
    Eq.x_marginal_probability = stats.integral.to.probability.apply(Integral[_x](Probability(x, y)))

    _y = pspace(y).symbol
    Eq.y_marginal_probability = stats.integral.to.probability.apply(Integral[_y](Probability(x, y)))

    Eq << stats.is_nonzero.imply.is_positive.apply(Eq[0])

    Eq <<= calculus.gt.imply.gt.integral.apply(Eq[-1], (_y,)), \
        calculus.gt.imply.gt.integral.apply(Eq[-1], (_x,))

    Eq <<= Eq[-2].subs(Eq.y_marginal_probability), Eq[-1].subs(Eq.x_marginal_probability)

    Eq <<= algebra.gt.imply.ne.apply(Eq[-1]) & algebra.gt.imply.ne.apply(Eq[-2])


if __name__ == '__main__':
    run()
