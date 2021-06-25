from util import *


@apply(given=None)
def apply(imply):
    from axiom.algebra.all.imply.ou import rewrite_as_Or
    return Equivalent(imply, rewrite_as_Or(imply))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << algebra.equivalent.given.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.imply.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.given.ou)


if __name__ == '__main__':
    run()

