from util import *


@apply
def apply(f0, suffice, n=None, start=0):
    start = sympify(start)
    fn, fn1 = suffice.of(Infer)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    a = n.domain.min()
    if a == start:
        return fn
    if a < start:
        diff = start - a
        if diff.is_Number:
            for i in range(diff):
                if fn._subs(n, a + i):
                    continue
                return
            return fn


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(LessEqual(f[0], g[0]), Infer(LessEqual(f[n], g[n]), LessEqual(f[n + 1], g[n + 1])), n=n)

    h = Symbol(Lamda[n](Bool(f[n] <= g[n])))

    Eq << h[0].this.definition

    Eq << algebra.cond.imply.eq.bool.apply(Eq[0])

    Eq.initial = algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq.suffice = Infer(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.lhs.apply(algebra.bool.to.piece)

    Eq << algebra.eq.infer.imply.eq.induct.apply(Eq.initial, Eq.suffice, n=n)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

from . import second
from . import split
# created on 2018-04-18
