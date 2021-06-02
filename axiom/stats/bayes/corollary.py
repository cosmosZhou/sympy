from util import *


# given: Probability(x) ! =0
# imply: Probability(x, y) = Probability(y | x) Probability(x)
@apply
def apply(given, var):
    assert given.is_Unequal
    x_probability, zero = given.args

    assert zero.is_zero
    eq = x_probability.arg
    if eq.is_Equal:
        x, _x = eq.args
        assert x.is_random and _x == pspace(x).symbol

        if var.is_Probability:
            joint_probability = var
            marginal_probability = joint_probability.marginalize(x)
            if marginal_probability is None:
                var = joint_probability.arg
                joint_probability = Probability(joint_probability.arg, x)
            else:
                var = marginal_probability.arg

            assert not var.is_Conditioned
            return Equal(joint_probability, Probability(var | x) * Probability(x))
        else:
            return Equal(Probability(x, var), Probability(var | x) * Probability(x))
    elif eq.is_Conditioned:
        x, _x = eq.lhs.args
        assert x.is_random and _x == pspace(x).symbol

        assert var.is_Probability
        joint_probability = var
        var = joint_probability.marginalize(x).arg
        assert var.is_Conditioned
        assert var.rhs == eq.rhs
        return Equal(joint_probability, Probability(var | x) * Probability(x, given=eq.rhs))
    else:
        assert eq.is_And
        assert var.is_random and var.is_symbol
        assert var.as_boolean() not in eq._argset
        return Equal(Probability(eq, var), Probability(var | eq) * Probability(eq))


@prove
def prove(Eq):
    from axiom import stats, algebra
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)

    given = Unequal(Probability(x), 0)

    Eq << apply(given, y)

    Eq << stats.bayes.theorem.apply(Eq[-1].lhs, x)

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()
