from util import *

from axiom.discrete.imply.gt_zero.alpha import alpha
from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K


@apply
def apply(x, wrt=None):
    n = x.shape[0]
    assert n.is_finite
    assert n >= 3

    if wrt is None:
        i = x.generate_var(integer=True, var='i')
    else:
        i = wrt

    return Infer(All[i:1:n](x[i] > 0), Equal(alpha(x), H(x) / K(x)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(x[:n + 1])

    Eq.initial = Eq[0].subs(n, 2)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << Eq[-1].this.lhs + 1

    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.ne_zero)

    Eq << algebra.infer.given.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.mul.ne_zero.eq)

    Eq << Eq[-1].this.rhs.lhs.ratsimp()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq.alpha_recurrence = discrete.imply.infer.alpha.recurrence.apply(Eq.induct.find(alpha))

    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], x[:n + 1], BlockMatrix(x[:n], x[n] + 1 / x[n + 1]))

    Eq << Eq[-1].this.rhs.lhs.apply(discrete.alpha.block)

    Eq << Eq[-1].this.lhs.apply(algebra.all.given.et, cond={n})

    Eq << Eq[-1].this.find(All)().expr.simplify()

    Eq << Eq[-1].this.find(Greater).apply(algebra.add_gt_zero.given.et.gt_zero)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_zero.given.gt_zero.inverse)

    Eq << Eq[-1].this.lhs.apply(algebra.et.to.all.limits.push_back)

    Eq <<= Eq.alpha_recurrence & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit)

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.rhs.ratsimp()

    Eq << Eq.induct.this.find(H).defun()

    Eq << Eq[-1].this.find(Indexed * ~H).defun()

    Eq << Eq[-1].this.find(Mul, Add).expand()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(Indexed * ~K).defun()

    Eq << Eq[-1].this.find(Pow, Add).expand()

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

# created on 2020-09-23
