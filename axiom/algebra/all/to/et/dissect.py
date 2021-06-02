from util import *
import axiom


@apply(given=None)
def apply(self, *, cond=None, wrt=None, evaluate=False):
    from axiom.algebra.sum.to.add.dissect import dissect
    assert self.is_ForAll
    return Equivalent(self, dissect(self, cond, wrt=wrt), evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(real=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(ForAll[x:A](f(x) > 0), cond=B)

    Eq << algebra.equivalent.given.suffice.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(algebra.et.given.all.limits_union)

    Eq << Eq[-1].this.lhs.apply(algebra.all.all.imply.all.limits_union)


if __name__ == '__main__':
    run()

