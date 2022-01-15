from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(MatProduct, self, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n, d = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(k, k))
    m = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(MatProduct[n:0:m](f(n)), d)

    Eq << Eq[0].subs(m, 0)

    Eq.induct = Eq[0].subs(m, m + 1)

    Eq << Eq.induct.this.lhs.apply(discrete.matProd.to.matmul.pop_back)

    Eq << Eq[-1].this.rhs.apply(discrete.matProd.to.matmul.pop_back)

    Eq << Eq[0] @ f(m)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=m, start=0)


if __name__ == '__main__':
    run()
# created on 2020-08-30
