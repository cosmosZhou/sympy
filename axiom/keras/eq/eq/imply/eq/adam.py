from util import *


def extract(recurrence):
    lhs, rhs = recurrence.args
    t, *_ = lhs.indices
    m = lhs.base

    p = rhs.as_poly(m[t - 1])
    if p is None or p.degree() != 1:
        return None
    beta = p.coeff_monomial(m[t - 1])
    beta_gt = p.coeff_monomial(1)

    gt = beta_gt / (1 - beta)
    gt = gt.ratsimp()

    g = gt.base
    return m, g, beta, t


@apply
def apply(initial_condition, recurrence):
    m, g, beta, t = extract(recurrence)
    assert initial_condition.is_Equal
    m0, _0 = initial_condition.args
    assert m0 == m[0] and _0.is_zero

    k = Symbol(integer=True, nonnegative=True)

    return Equal(m[k], beta ** k * (1 - beta) * Sum[t:1:k + 1](beta ** (-t) * g[t]))


@prove
def prove(Eq):
    from axiom import algebra

    m, g = Symbol(shape=(oo,), real=True)
    t = Symbol(integer=True, positive=True)
    beta = Symbol(real=True, nonzero=True)
#     beta = Symbol.beta(real=True, zero=False)
    Eq << apply(Equal(m[0], 0), Equal(m[t], beta * m[t - 1] + (1 - beta) * g[t]))

    Eq << Eq[1] / beta ** t

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Eq[-1].this.rhs.collect(g[t])

    k = Eq[2].lhs.indices[0]
    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (t, 1, k + 1))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] * beta ** k

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.mul.split.exponent)

    Eq << Eq[-1].this.find(Add).apply(algebra.add.to.mul)


if __name__ == '__main__':
    run()

# created on 2020-12-22
