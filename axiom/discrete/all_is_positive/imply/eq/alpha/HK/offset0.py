from util import *

import axiom

from axiom.discrete.imply.is_positive.alpha import alpha
from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    xj, *limits = axiom.all_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 0
    x, _j = xj.of(Indexed)
    offset = _j - j
    if offset != 0:
        assert not offset._has(j)
        x = x[offset:]
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    Eq << apply(ForAll[i:0:n](x[i] > 0))

    x_ = Symbol.x(real=True, positive=True, shape=(oo,))
    Eq << discrete.alpha.to.mul.HK.st.is_positive.apply(alpha(x_[:n]))

    Eq << Eq[-1].subs(x_[:n], x[:n])

    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

