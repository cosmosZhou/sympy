from util import *

import axiom
from axiom.discrete.K.to.add.definition import K

from axiom.discrete.imply.is_positive.alpha import alpha


def reverse(x):
    n = x.shape[0]
    i = x.generate_var(integer=True, free_symbols='i')
    return Lamda[i:n](x[n - 1 - i])


@apply
def apply(x):
    n = x.shape[0]
    assert x.is_positive
    n -= 1
    assert n >= 1
    return Equal(alpha(reverse(x[1:n + 1])), K(x[:n + 1]) / K(x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, positive=True, shape=(oo,))
#     x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)

    Eq << apply(x[:n + 1])

    Eq.initial = Eq[0].subs(n, 1)

    Eq << Eq.initial.this.find(alpha).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << discrete.imply.is_nonzero.alpha.apply(reverse(x[1:n + 1]))

    Eq << algebra.is_nonzero.eq.imply.eq.inverse.apply(Eq[-1], Eq[0])

    Eq << Eq.induct.induct()

    Eq << algebra.eq.suffice.imply.eq.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

