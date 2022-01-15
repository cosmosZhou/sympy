from util import *


@apply(given=None)
def apply(imply):
    from axiom.algebra.all.imply.ou import rewrite_as_Or
    return Equivalent(imply, rewrite_as_Or(imply), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.imply.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.given.ou)


if __name__ == '__main__':
    run()

# created on 2018-12-23
