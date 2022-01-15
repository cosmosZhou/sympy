from util import *


@apply
def apply(given, wrt=None):
    (x, yzw), (_x, w) = given.of(Equal[Conditioned, Conditioned])
    assert x == _x

    assert w in yzw.args
    args = [*yzw.args]
    args.remove(w)
    y, z = args

    if wrt is not None:
        if y.is_Equal:
            y = y.lhs
        if z.is_Equal:
            z = z.lhs

        assert wrt in {y, z}
        return Equal(x | wrt.as_boolean() & w, x | w)
    return Equal(x | y & w, x | w)


@prove(proved=False)
def prove(Eq):
    from axiom import stats, algebra, calculus

    x, y, z, w = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y.as_boolean() & z.as_boolean() & w.as_boolean(), x | w), wrt=y)

    return
    Eq << stats.eq_conditioned.imply.is_nonzero.apply(Eq[0])
    Eq.xyz_nonzero, Eq.w_nonzero = algebra.et.imply.conds.apply(Eq[-1])
    Eq << stats.is_nonzero.imply.et.apply(Eq.xyz_nonzero)
    Eq.y_nonzero, Eq.z_nonzero = algebra.et.imply.cond.apply(Eq[-1], index=slice(1, 3))
    Eq.xy_probability = stats.bayes.corollary.apply(Eq.y_nonzero, var=x | w)
    Eq << stats.is_nonzero.imply.is_nonzero.conditioned.apply(Eq.xyz_nonzero, wrt=w)
    Eq << stats.is_nonzero.imply.eq.bayes.apply(Probability(x | w, y, z), y, z)
    Eq << algebra.all.imply.ou.apply(Eq[-1])
    Eq <<= Eq[-1] & Eq[-3]
    Eq << algebra.et.imply.conds.apply(Eq[-1])
    Eq << Eq[-1].subs(Eq[0])
    Eq <<= stats.total_probability_theorem.apply(Eq[-1].lhs, z), \
        stats.total_probability_theorem.apply(Eq[-1].rhs.args[0], z), \
        calculus.eq.imply.eq.integral.apply(Eq[-1], (pspace(z).symbol,))
    Eq << Eq[-3].subs(Eq.xy_probability)
    Eq << Eq[-1].subs(Eq[-2])
    Eq << Eq[-1].subs(Eq[-4])
    Eq << algebra.ne_zero.eq.imply.eq.scalar.apply(Eq[-1], Eq.y_nonzero)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-07-14
