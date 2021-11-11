from util import *

from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K

from axiom.discrete.imply.gt_zero.alpha import alpha


@apply
def apply(x):
    n = x.shape[0]
    n -= 1
    assert x.is_positive
    assert n > 0
    return Equal(K(x[1:n + 1]) / H(x[1:n + 1]), H(x[:n + 1]) / K(x[:n + 1]) - x[0])


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)

    Eq << apply(x[:n + 1])

    Eq << discrete.alpha.to.mul.HK.st.gt_zero.apply(alpha(x[:n + 1]))

    Eq << Eq[-1].this.lhs.defun()

    Eq << discrete.alpha.to.mul.HK.st.gt_zero.apply(alpha(x[1:n + 1]))

    Eq << algebra.eq.eq.imply.eq.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1] - x[0]


if __name__ == '__main__':
    run()

# created on 2020-09-25
# updated on 2020-09-25
