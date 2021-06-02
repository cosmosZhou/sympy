from util import *

import axiom

from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(given):
    xj, *limits = axiom.all_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)

    x, _j = xj.of(Indexed)
    offset = _j - j
    if offset != 0:
        assert not offset._has(j)

    a += offset
    n += offset
    return Unequal(alpha(x[a:n]), 0)


@prove
def prove(Eq):
    from axiom import discrete
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(integer=True, nonnegative=True)
    b = Symbol.b(integer=True)
    i = Symbol.i(integer=True)

    Eq << apply(ForAll[i:a:n](x[i + b] > 0))

    x_ = Symbol.x(x[a + b:])

    Eq << x_[i].this.definition

    Eq << Eq[0].limits_subs(i, i + a)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << discrete.all_is_positive.imply.is_nonzero.alpha.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.arg.definition


if __name__ == '__main__':
    run()
