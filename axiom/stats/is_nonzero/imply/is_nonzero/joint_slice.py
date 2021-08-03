from util import *


@apply
def apply(given, indices):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero

    eqs = given.lhs.arg
    assert eqs.is_And

    args = []
    for eq, t in zip(eqs.args, indices):
        x, _x = eq.args
        assert _x == pspace(x).symbol
        args.append(x[t])

    return Unequal(Probability(*args), 0)


@prove
def prove(Eq):
    from axiom import algebra, stats

    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(real=True, shape=(n,), random=True)
    y = Symbol.y(real=True, shape=(n,), random=True)
    t = Symbol.t(domain=Range(1, n))
    Eq << apply(Unequal(Probability(x, y), 0), [slice(0, t), slice(0, t)])

    Eq << Eq[0].this.lhs.arg.args[-1].apply(algebra.eq.imply.et.eq.blockmatrix, t)

    Eq << Eq[-1].this.lhs.arg.args[0].apply(algebra.eq.imply.et.eq.blockmatrix, t)

    Eq << stats.is_nonzero.imply.et.apply(Eq[-1])

    Eq << stats.is_nonzero.imply.is_nonzero.delete.apply(Eq[-2], index=1)


if __name__ == '__main__':
    run()
