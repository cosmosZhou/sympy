from util import *


def assumptions():
    # d is the number of output labels
    # oo is the length of the sequence
    d = Symbol.d(domain=Range(2, oo))
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), domain=Range(0, d), random=True, given=True)

    k = Symbol.k(domain=Range(1, n))
    return Equal(x[k] | x[:k].as_boolean() & y[:k].as_boolean(), x[k]), Equal(y[k] | y[:k], y[k] | y[k - 1]), Equal(y[k] | x[:k], y[k]), Unequal(Probability(x, y), 0)


def process_assumptions(*given):
    x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption = given
    assert xy_nonzero_assumption.is_Unequal
    assert xy_nonzero_assumption.rhs.is_zero

    x = x_independence_assumption.rhs.base
    y = y_independence_assumption.lhs.lhs.base
    assert y_independence_assumption.lhs.lhs == y_independence_assumption.rhs.lhs

    assert xy_nonzero_assumption.lhs == Probability(x, y)

    assert xy_independence_assumption.rhs.base == y
    return x, y


@apply
def apply(*given):
    x, y = process_assumptions(*given)
    n, _ = x.shape
    t = Symbol.t(integer=True, domain=Range(0, n))
    i = Symbol.i(integer=True)

    return Equal(Probability(x[:t + 1], y[:t + 1]),
                    Probability(x[0] | y[0]) * Probability(y[0]) * Product[i:1:t + 1](Probability(y[i] | y[i - 1]) * Probability(x[i] | y[i])))


@prove
def prove(Eq):
    from axiom import stats, algebra

    Eq.x_independence, Eq.y_independence, Eq.xy_independence, Eq.xy_nonzero_assumption, Eq.factorization = apply(*assumptions())

    y, k = Eq.y_independence.rhs.lhs.args

    Eq << Eq.x_independence.domain_definition()

    Eq << algebra.et.imply.conds.apply(stats.is_nonzero.imply.et.apply(Eq[-1]))

    Eq << stats.is_nonzero.imply.is_nonzero.conditioned.apply(Eq[-3], y[:k])

    Eq << stats.bayes.corollary.apply(Eq[-2], var=Eq[0].lhs.subs(k, k + 1))

    Eq << stats.bayes.corollary.apply(Eq[-2], var=Eq[-1].rhs.args[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.xy_joint_probability = stats.bayes.corollary.apply(Eq[2], var=Eq[0].lhs)

    Eq << Eq[-1].subs(Eq.xy_joint_probability.reversed)

    Eq.recursion = algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[0], Eq[-1])

    Eq << stats.is_nonzero.imply.is_nonzero.joint_slice.apply(Eq.xy_nonzero_assumption, [k, k])

    Eq << stats.eq.imply.eq.single_condition.apply(Eq.x_independence)

    Eq << stats.eq.eq.is_nonzero.imply.eq.joint_nonzero.apply(Eq[-1], Eq.xy_independence, Eq[-2])

    Eq << stats.eq.is_nonzero.imply.eq.joint_probability.apply(Eq[-1], Eq[0])

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq << stats.bayes.theorem.apply(Eq.recursion.rhs, y[k])

    Eq.or_statement = algebra.all.imply.ou.apply(Eq[-1])

    Eq << algebra.cond.imply.ou.subs.apply(Eq[2], k, k + 1)

    Eq << Eq[-1].this.find(NotContains).simplify()

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=1)

    _, Eq.y_nonzero_assumption = algebra.et.imply.conds.apply(stats.is_nonzero.imply.et.apply(Eq.xy_nonzero_assumption))
    Eq <<= Eq[-1] & Eq.y_nonzero_assumption

    Eq.y_joint_y_historic = Eq[-1].this.lhs.arg.apply(algebra.eq.imply.et.split.blockmatrix, Slice[-1:])

    Eq << stats.is_nonzero.imply.is_nonzero.conditioned.apply(Eq.y_joint_y_historic, y[:k])

    Eq << algebra.et.imply.conds.apply(Eq[-1] & Eq.or_statement)

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq.recursion = Eq.recursion.subs(Eq.y_independence)

    Eq << stats.eq.imply.eq.single_condition.apply(Eq.x_independence, wrt=y[:k])

    Eq << stats.eq.is_nonzero.imply.eq.joint_probability.apply(Eq.y_joint_y_historic, Eq[-1])

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq << algebra.eq.imply.eq.product.apply(Eq.recursion, (k, 1, k + 1))

    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, Eq.factorization.rhs.args[-1].variable)

    Eq << Eq[-1] * Eq[-1].lhs.args[0].base

    Eq.first = Eq.xy_joint_probability.subs(k, 1)

    Eq << Eq[-1].subs(Eq.first)

    t = Eq.factorization.rhs.args[-1].limits[0][2] - 1

    Eq << algebra.cond.imply.ou.subs.apply(Eq[-1], k, t)

    Eq << Eq[-1].this.find(NotContains).simplify()

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=-1)

    Eq <<= Eq[-1] & Eq.first


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    run()
