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

    assert x.is_positive
    return Equal(A, alpha(x[:n], x[n] + 1 / x[n + 1]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)

    Eq << apply(alpha(x[:n + 2]))

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << algebra.eq.imply.eq.subs.apply(Eq[0], x[:n + 2], x[1:n + 3])

    Eq << discrete.imply.ne_zero.alpha.apply(x[1:n + 3])

    Eq << algebra.ne_zero.eq.imply.eq.inverse.apply(Eq[-1], Eq[-2])

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-09-18
# updated on 2020-09-18
