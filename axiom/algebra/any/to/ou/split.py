from util import *


@apply(given=None)
def apply(self, indices, wrt=None, evaluate=False):
    from axiom.algebra.sum.to.add.split import split
    return Equivalent(self, split(Any, self, indices, wrt=wrt), evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Any[x:A](f(x) > 0), B)

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.ou, cond=B)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.ou, cond=B)


if __name__ == '__main__':
    run()

# created on 2019-02-11
