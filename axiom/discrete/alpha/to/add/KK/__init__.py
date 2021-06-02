from util import *

import axiom
from axiom.discrete.K.to.add.definition import K

from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(x):
    n = x.shape[0]
    n -= 1
    assert n >= 1
    return Equal(alpha(x[:n + 1]), alpha(x[:n]) + (-1) ** (n + 1) / (K(x[:n + 1]) * K(x[:n])))


@prove
def prove(Eq):
    from axiom import discrete
    x = Symbol.x(real=True, positive=True, shape=(oo,))
#     x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(x[:n + 1])

    Eq << Eq[0].this.lhs.apply(discrete.alpha.to.mul.HK.st.is_positive)

    Eq << Eq[-1].this.find(alpha).apply(discrete.alpha.to.mul.HK.st.is_positive)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.lhs.together()

    Eq << discrete.continued_fraction.HK.recurrence.apply(x[:n + 1])


if __name__ == '__main__':
    run()

from . import step2
