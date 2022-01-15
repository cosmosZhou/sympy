from util import *


def KL(p, q):
    cond_p = p.of(Probability)
    cond_q = q.of(Probability)
    if cond_p.is_Equal:
        X, x = cond_p.args
        _X, _x = cond_q.of(Equal)
        assert x == _x
        return Sum[x](p * log(p / q))
    elif cond_p.is_Conditioned:
        cond_p, given = cond_p.args
        cond_q, _given = cond_q.of(Conditioned)
        if cond_p.is_Equal:
            X, x = cond_p.args
            _X, _x = cond_q.of(Equal)
            assert x == _x
            return Sum[x](p * log(p / q))
    else:
        conds_p = cond_p.of(And)
        conds_q = cond_q.of(And)

        symbol2value = {}
        for cond in conds_p:
            X, x = cond.of(Equal)
            symbol2value[x] = X

        for cond in conds_q:
            X, x = cond.of(Equal)
            assert x in symbol2value

        return Sum[tuple(symbol2value.keys())](p * log(p / q))


@apply
def apply(X, Y, x=None):
    if x is None:
        x = X.generate_var(Y, var='x', **X.type.dict)

    return GreaterEqual(KL(Probability(Equal(X, x)), Probability(Equal(Y, x))), 0)


@prove
def prove(Eq):
    from axiom import algebra, stats

    X = Symbol(random=True, integer=True)
    X_ = Symbol("X'", random=True, integer=True)
    Eq << apply(X, X_)

    Eq << algebra.imply.ge.log.apply(Eq[0].find(Log).arg)

    Eq << algebra.ge.imply.ge.mul.apply(Eq[-1], Eq[0].find(Probability))

    x = Eq[0].lhs.variable
    Eq << algebra.ge.imply.ge.sum.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.args[0].apply(stats.sum.to.one)
    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one)


if __name__ == '__main__':
    run()

from . import conditioned
# created on 2021-07-20
