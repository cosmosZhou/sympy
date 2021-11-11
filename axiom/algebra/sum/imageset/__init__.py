from util import *


@apply
def apply(self):
    f, (m, domain) = self.of(Sum)
    n, expr, base_set = domain.image_set()

    assert expr.as_poly(n).degree() == 1
    f = f._subs(m, expr)

    return Equal(self, self.func(f, (n, base_set)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, a, b, m = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    h = Function(real=True)
    t = Function(integer=True)
    Eq << apply(Sum[n:imageset(n, a * n + b, h(n) > 0)](f[n]))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.lhs.limits_subs(n, m)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.subs.offset, b)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, b)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.absorb)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.imageset.proportional)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.absorb)


if __name__ == '__main__':
    run()
from . import proportional
# created on 2018-05-02
# updated on 2018-05-02
