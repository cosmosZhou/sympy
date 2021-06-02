from util import *


# given: x | y & z = x
# imply: x | y = x
@apply
def apply(given, wrt=None):

    assert given.is_Equal
    lhs, rhs = given.args
    assert lhs.is_Conditioned
    x, yzw = lhs.args
    assert rhs.is_Conditioned
    _x, w = rhs.args
    assert x == _x

    assert w in yzw.args
    args = [*yzw.args]
    args.remove(w)
    y, z = args
#     assert w in yzw._argset
#     y, z = {*yzw.args} - {w}

    if wrt is not None:
        if y.is_Equal:
            y = y.lhs
        if z.is_Equal:
            z = z.lhs

        assert wrt in {y, z}
        return Equal(x | wrt.as_boolean() & w, x | w)
    return Equal(x | y & w, x | w)


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    w = Symbol.w(real=True, random=True)

    Eq << apply(Equal(x | y.as_boolean() & z.as_boolean() & w.as_boolean(), x | w), wrt=y)

    Eq << Eq[0].domain_definition()

    Eq.xyz_nonzero, Eq.w_nonzero = algebra.et.imply.conds.apply(Eq[-1])

    Eq << stats.is_nonzero.imply.et.apply(Eq.xyz_nonzero)

    Eq.y_nonzero, Eq.z_nonzero = algebra.et.imply.cond.apply(Eq[-1], index=Slice[1:3])

    Eq.xy_probability = stats.bayes.corollary.apply(Eq.y_nonzero, var=x | w)

    Eq << stats.is_nonzero.imply.is_nonzero.conditioned.apply(Eq.xyz_nonzero, wrt=w)

    Eq << stats.bayes.theorem.apply(Probability(x | w, y, z), y, z)

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

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[-1], Eq.y_nonzero)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

