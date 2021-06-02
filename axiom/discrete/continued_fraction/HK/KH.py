from util import *

from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K

from axiom.discrete.imply.is_positive.alpha import alpha


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
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(x[:n + 1])

    Eq << discrete.alpha.to.mul.HK.st.is_positive.apply(alpha(x[:n + 1]))

    Eq << Eq[-1].this.lhs.defun()

    Eq << discrete.alpha.to.mul.HK.st.is_positive.apply(alpha(x[1:n + 1]))

    Eq << algebra.eq.eq.imply.eq.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1] - x[0]


if __name__ == '__main__':
    run()

