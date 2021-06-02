from util import *


@apply
def apply(*given):
    x_equality, inequality = given

    assert inequality.is_Unequal
    xy_probability, zero = inequality.args
    assert xy_probability.is_Probability
    assert zero.is_zero
    xy_joint = xy_probability.arg

    assert x_equality.is_Equal

    x_t_given, x_t = x_equality.args

    assert x_t_given.is_Conditioned
    _x_t, x_t_historic = x_t_given.args

    assert x_t == _x_t

    x, t = x_t.args
    assert x_t_historic == x[:t].as_boolean()
    x_boolean, y_boolean = xy_joint._argset
    if x_boolean != x.as_boolean():
        x_boolean, y_boolean = y_boolean, x_boolean

    y = y_boolean.lhs

    assert t.is_positive
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    return Equal(ArgMax[i](Probability(y[i] | x)), ArgMax[i](Probability(y[i]) * Product[j](Probability(x[j] | y[i]))))


@prove
def prove(Eq):
    from axiom import stats, algebra
    t = Symbol.t(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,), random=True)
    y = Symbol.y(real=True, shape=(m,), random=True)

    Eq << apply(Equal(x[t] | x[:t], x[t]), Unequal(Probability(x, y), 0))

    i = Eq[-1].lhs.variable
    j = Eq[-1].rhs.function.args[-1].variable

    Eq << stats.is_nonzero.imply.et.apply(Eq[1])

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << stats.bayes.corollary.apply(Eq[-2], var=y[i])

    Eq.y_given_x = algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[-1], Eq[-3]).reversed

    Eq << stats.is_nonzero.imply.is_nonzero.joint_slice.apply(Eq[1], [j, i])

    Eq << stats.is_nonzero.imply.et.apply(Eq[-1])

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << stats.bayes.corollary.apply(Eq[-1], var=x)

    Eq.y_given_x = Eq.y_given_x.subs(Eq[-1])

    Eq << algebra.eq.imply.eq.argmax.apply(Eq.y_given_x, (i,))

    Eq << stats.is_nonzero.imply.is_nonzero.joint_slice.apply(Eq[1], Slice[:t, i])

    Eq.xt_given_x_historic = stats.eq.is_nonzero.imply.eq.joint_probability.apply(Eq[0], Eq[-1])

    Eq.xt_given_yi_nonzero = stats.is_nonzero.imply.is_nonzero.conditioned.apply(Eq[-1], wrt=y[i])

    Eq << stats.bayes.theorem.apply(Probability(x[:t + 1] | y[i]), x[:t])

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq.xt_given_yi_nonzero

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.xt_given_x_historic)

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[-1], Eq.xt_given_yi_nonzero)

    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (t, 1, n))

    t = Eq[-1].rhs.variable
    Eq << Eq[-1] / Eq[-1].lhs.args[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.product.limits.absorb.front)

    Eq << Eq[-1].this.rhs.limits_subs(t, j)

    Eq << Eq[2].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
