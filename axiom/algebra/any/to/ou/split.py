from util import *


@apply(given=None)
def apply(self, indices, wrt=None, evaluate=False):
    from axiom.algebra.sum.to.add.split import split
    assert self.is_Any
    return Equivalent(self, split(self, indices, wrt=wrt), evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(real=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Any[x:A](f(x) > 0), B)

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.ou, cond=B)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.ou, cond=B)


if __name__ == '__main__':
    run()

