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
def apply(*given):
    initial_condition, recurrence = given
    m, g, beta, t = extract(recurrence)
    assert initial_condition.is_Equal
    m0, _0 = initial_condition.args
    assert m0 == m[0] and _0.is_zero

    k = Symbol.k(integer=True, nonnegative=True)

    return Equal(m[k], beta ** k * (1 - beta) * Sum[t:1:k + 1](beta ** (-t) * g[t]))


@prove
def prove(Eq):
    from axiom import algebra
    m = Symbol.m(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)
    t = Symbol.t(integer=True, positive=True)
    beta = Symbol.beta(real=True, nonzero=True)
    recurrence = Equal(m[t], beta * m[t - 1] + (1 - beta) * g[t])
    initial_condition = Equal(m[0], 0)

    Eq << apply(initial_condition, recurrence)

    Eq << Eq[1] / beta ** t

    Eq << Eq[-1].expand()

    Eq << Eq[-1].powsimp()

    Eq << Eq[-1].collect(g[t])

    k = Eq[2].lhs.indices[0]

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (t, 1, k + 1))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].solve(m[k])


if __name__ == '__main__':
    run()

