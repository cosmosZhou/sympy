from util import *

from axiom.discrete.imply.is_positive.alpha import alpha
from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    assert _j == j
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    j = Symbol.j(integer=True)

    Eq << apply(All[j:1:n](x[j] > 0))

    Eq << algebra.cond.given.suffice.split.apply(Eq[1], cond=n >= 3)

    Eq.case1, Eq.case2 = algebra.suffice.given.suffice.split.apply(Eq[-1], cond=n < 2)

    Eq << Eq.case1.this.lhs.apply(algebra.lt.to.eq.squeeze)

    Eq << Eq[-1].this.apply(algebra.suffice.subs)

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq.case2.this.apply(algebra.suffice.subs)

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.rhs.expand()

    n_ = Symbol.n(domain=Range(3, oo))
    Eq << discrete.imply.suffice.alpha.HK.apply(x[:n_], wrt=j)

    Eq << Eq[0].subs(n, n_)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.cond.imply.all.apply(Eq[-1], n_)

    _n = Eq[-1].variable
    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << Eq[-1].subs(_n, n)


if __name__ == '__main__':
    run()

from . import offset0
