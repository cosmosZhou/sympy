from util import *



@apply
def apply(given):
    p, q = given.of(Infer)

    return Equal(Bool(p), Bool(p) * Bool(q))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Infer(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Infer(Equal(Bool(Eq[0].lhs), 1), Equal(Bool(Eq[0].rhs), 1), plausible=True)

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.rhs.lhs.apply(algebra.bool.to.piece)

    Eq << Eq[-2].apply(algebra.infer.imply.ou)

    Eq << Eq[-1].this.args[1].apply(algebra.ne.imply.is_zero.bool)

    Eq << algebra.ou.imply.is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    run()
# created on 2018-01-27
