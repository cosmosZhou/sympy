from util import *


# given: x | y = x
# imply: x | y & z = x | z
@apply
def apply(*given):
    equality, unequal = given
    assert unequal.is_Unequal
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero
    assert unequal.lhs.arg.is_Conditioned
    z, _y = unequal.lhs.arg.args

    assert equality.is_Equal
    lhs, rhs = equality.args
    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs

    if _y != y:
        _y, z = z, _y

    assert _y == y

    return Equal(x | y & z, x | z)


@prove
def prove(Eq):
    from axiom import stats, algebra
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)

    Eq << apply(Equal(x | y, x), Unequal(Probability(z | y), 0))

    Eq << stats.bayes.theorem.apply(Probability(x | y, z), z)

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0])

    Eq << stats.is_nonzero.imply.is_nonzero.marginal.apply(Eq[1])

    Eq << stats.bayes.corollary.apply(Eq[-1], var=x)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
