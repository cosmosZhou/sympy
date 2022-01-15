from util import *


@apply
def apply(cond, equivalent):
    lhs, rhs = equivalent.of(Equivalent)
    if cond != lhs:
        lhs, rhs = rhs, lhs
    assert cond == lhs
    return rhs


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(LessEqual(f[0], g[0]), Equivalent(LessEqual(f[0], g[0]), LessEqual(f[n], g[n])))

    Eq << algebra.iff.imply.infer.apply(Eq[1])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-17
