from util import *


@apply
def apply(imply):
    from axiom.algebra.all.imply.ou import rewrite_as_Or
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << ~Eq[0]

    Eq << algebra.any.imply.any_et.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.cond.imply.eq.bool, split=False)

    Eq << algebra.cond.imply.eq.bool.invert.apply(Eq[1])

    Eq << Eq[-2].this.expr.apply(algebra.eq.eq.imply.eq.transit, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-17
