from util import *

from axiom.discrete.imply.gt_zero.alpha import alpha


@apply
def apply(A):
    assert A.is_alpha
    assert len(A.args) == 1
    x = A.arg
    n = x.shape[0] - 2

    assert n > 0
    x = x.base

    i = A.generate_var(integer=True, var='i')
    return Infer(All[i:1:n + 2](x[i] > 0), Equal(A, alpha(x[:n], x[n] + 1 / x[n + 1])))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(alpha(x[:n + 2]))

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(alpha).defun()

    Eq << Eq[-1].this.rhs.rhs.defun()

    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], x[:n + 2], x[1:n + 3])

    Eq << Eq[-1].this.lhs.apply(algebra.all.limits.subs.offset, -1)

    Eq << Eq[-1].this.lhs.apply(algebra.all.given.all.limits.relax, domain=Range(1, n + 3))

    i = Eq[0].lhs.variable
    Eq << Infer(All[i:1:n + 3](x[i] > 0), Unequal(alpha(x[1:n + 3]), 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(discrete.all_gt_zero.imply.ne_zero.alpha.offset)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.eq.imply.eq.inverse)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-09-23
# updated on 2020-09-23
